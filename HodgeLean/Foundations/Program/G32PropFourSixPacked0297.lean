import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0296

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_025 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 25 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_025_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 0 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 13 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 0 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 0 13 14, g32p_row02_traceSegment_025_0000_0013, g32p_row02_traceSegment_025_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 27 13 14, g32p_row02_traceSegment_025_0027_0013, g32p_row02_traceSegment_025_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 0 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 0 27 27, g32p_row02_traceSegment_025_0000_0027, g32p_row02_traceSegment_025_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 67 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 54 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 54 13 14, g32p_row02_traceSegment_025_0054_0013, g32p_row02_traceSegment_025_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 81 13 14, g32p_row02_traceSegment_025_0081_0013, g32p_row02_traceSegment_025_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 54 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 54 27 27, g32p_row02_traceSegment_025_0054_0027, g32p_row02_traceSegment_025_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 0 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 0 54 54, g32p_row02_traceSegment_025_0000_0054, g32p_row02_traceSegment_025_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 121 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 108 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 108 13 14, g32p_row02_traceSegment_025_0108_0013, g32p_row02_traceSegment_025_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 148 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 135 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 135 13 14, g32p_row02_traceSegment_025_0135_0013, g32p_row02_traceSegment_025_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 108 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 108 27 27, g32p_row02_traceSegment_025_0108_0027, g32p_row02_traceSegment_025_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 162 13 14, g32p_row02_traceSegment_025_0162_0013, g32p_row02_traceSegment_025_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 189 13 14, g32p_row02_traceSegment_025_0189_0013, g32p_row02_traceSegment_025_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 162 27 27, g32p_row02_traceSegment_025_0162_0027, g32p_row02_traceSegment_025_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 108 108 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 108 54 54, g32p_row02_traceSegment_025_0108_0054, g32p_row02_traceSegment_025_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 0 216 = [0, 0, 0, 3, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 0 108 108, g32p_row02_traceSegment_025_0000_0108, g32p_row02_traceSegment_025_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 216 13 14, g32p_row02_traceSegment_025_0216_0013, g32p_row02_traceSegment_025_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 256 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 243 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 243 13 14, g32p_row02_traceSegment_025_0243_0013, g32p_row02_traceSegment_025_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 216 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 216 27 27, g32p_row02_traceSegment_025_0216_0027, g32p_row02_traceSegment_025_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 270 13 14, g32p_row02_traceSegment_025_0270_0013, g32p_row02_traceSegment_025_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 297 13 14, g32p_row02_traceSegment_025_0297_0013, g32p_row02_traceSegment_025_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 270 27 27, g32p_row02_traceSegment_025_0270_0027, g32p_row02_traceSegment_025_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 216 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 216 54 54, g32p_row02_traceSegment_025_0216_0054, g32p_row02_traceSegment_025_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 337 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 324 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 324 13 14, g32p_row02_traceSegment_025_0324_0013, g32p_row02_traceSegment_025_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 351 13 = [0, 0, 0, 2, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 364 14 = [0, 0, 0, 5, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 351 27 = [0, 0, 0, 7, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 351 13 14, g32p_row02_traceSegment_025_0351_0013, g32p_row02_traceSegment_025_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 324 54 = [0, 0, 0, 9, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 324 27 27, g32p_row02_traceSegment_025_0324_0027, g32p_row02_traceSegment_025_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 378 13 = [0, 0, 0, 3, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 391 14 = [0, 0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 378 27 = [0, 0, 0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 378 13 14, g32p_row02_traceSegment_025_0378_0013, g32p_row02_traceSegment_025_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 405 13 = [0, 0, 0, 2, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 418 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 405 27 = [0, 0, 0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 405 13 14, g32p_row02_traceSegment_025_0405_0013, g32p_row02_traceSegment_025_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 378 54 = [0, 0, 0, 7, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 378 27 27, g32p_row02_traceSegment_025_0378_0027, g32p_row02_traceSegment_025_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 324 108 = [0, 0, 0, 16, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 324 54 54, g32p_row02_traceSegment_025_0324_0054, g32p_row02_traceSegment_025_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 216 216 = [0, 0, 0, 18, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 216 108 108, g32p_row02_traceSegment_025_0216_0108, g32p_row02_traceSegment_025_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_025 0 432 = [0, 0, 0, 21, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 0 216 216, g32p_row02_traceSegment_025_0000_0216, g32p_row02_traceSegment_025_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 445 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 432 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 432 13 14, g32p_row02_traceSegment_025_0432_0013, g32p_row02_traceSegment_025_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 459 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 472 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 459 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 459 13 14, g32p_row02_traceSegment_025_0459_0013, g32p_row02_traceSegment_025_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 432 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 432 27 27, g32p_row02_traceSegment_025_0432_0027, g32p_row02_traceSegment_025_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 486 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 499 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 486 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 486 13 14, g32p_row02_traceSegment_025_0486_0013, g32p_row02_traceSegment_025_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 513 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 513 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 513 13 14, g32p_row02_traceSegment_025_0513_0013, g32p_row02_traceSegment_025_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 486 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 486 27 27, g32p_row02_traceSegment_025_0486_0027, g32p_row02_traceSegment_025_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 432 108 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 432 54 54, g32p_row02_traceSegment_025_0432_0054, g32p_row02_traceSegment_025_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 540 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 553 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 540 27 = [0, 0, 0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 540 13 14, g32p_row02_traceSegment_025_0540_0013, g32p_row02_traceSegment_025_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 580 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 567 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 567 13 14, g32p_row02_traceSegment_025_0567_0013, g32p_row02_traceSegment_025_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 540 54 = [0, 0, 0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 540 27 27, g32p_row02_traceSegment_025_0540_0027, g32p_row02_traceSegment_025_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 594 13 14, g32p_row02_traceSegment_025_0594_0013, g32p_row02_traceSegment_025_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 621 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 621 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 621 13 14, g32p_row02_traceSegment_025_0621_0013, g32p_row02_traceSegment_025_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 594 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 594 27 27, g32p_row02_traceSegment_025_0594_0027, g32p_row02_traceSegment_025_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 540 108 = [0, 0, 0, 5, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 540 54 54, g32p_row02_traceSegment_025_0540_0054, g32p_row02_traceSegment_025_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 432 216 = [0, 0, 0, 12, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 432 108 108, g32p_row02_traceSegment_025_0432_0108, g32p_row02_traceSegment_025_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 648 13 14, g32p_row02_traceSegment_025_0648_0013, g32p_row02_traceSegment_025_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 675 13 14, g32p_row02_traceSegment_025_0675_0013, g32p_row02_traceSegment_025_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 648 27 27, g32p_row02_traceSegment_025_0648_0027, g32p_row02_traceSegment_025_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 715 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 702 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 702 13 14, g32p_row02_traceSegment_025_0702_0013, g32p_row02_traceSegment_025_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 729 13 14, g32p_row02_traceSegment_025_0729_0013, g32p_row02_traceSegment_025_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 702 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 702 27 27, g32p_row02_traceSegment_025_0702_0027, g32p_row02_traceSegment_025_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 648 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 648 54 54, g32p_row02_traceSegment_025_0648_0054, g32p_row02_traceSegment_025_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 769 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 756 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 756 13 14, g32p_row02_traceSegment_025_0756_0013, g32p_row02_traceSegment_025_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 783 13 14, g32p_row02_traceSegment_025_0783_0013, g32p_row02_traceSegment_025_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 756 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 756 27 27, g32p_row02_traceSegment_025_0756_0027, g32p_row02_traceSegment_025_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 810 13 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 823 14 = [0, 0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 810 27 = [0, 0, 0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 810 13 14, g32p_row02_traceSegment_025_0810_0013, g32p_row02_traceSegment_025_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 837 13 14, g32p_row02_traceSegment_025_0837_0013, g32p_row02_traceSegment_025_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 810 54 = [0, 0, 0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 810 27 27, g32p_row02_traceSegment_025_0810_0027, g32p_row02_traceSegment_025_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 756 108 = [0, 0, 0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 756 54 54, g32p_row02_traceSegment_025_0756_0054, g32p_row02_traceSegment_025_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 648 216 = [0, 0, 0, 1, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 648 108 108, g32p_row02_traceSegment_025_0648_0108, g32p_row02_traceSegment_025_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_025 432 432 = [0, 0, 0, 13, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 432 216 216, g32p_row02_traceSegment_025_0432_0216, g32p_row02_traceSegment_025_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_025 0 864 = [0, 0, 0, 34, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 0 432 432, g32p_row02_traceSegment_025_0000_0432, g32p_row02_traceSegment_025_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 864 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 864 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 864 13 14, g32p_row02_traceSegment_025_0864_0013, g32p_row02_traceSegment_025_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 904 14 = [0, 0, 0, 3, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 891 27 = [0, 0, 0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 891 13 14, g32p_row02_traceSegment_025_0891_0013, g32p_row02_traceSegment_025_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 864 54 = [0, 0, 0, 4, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 864 27 27, g32p_row02_traceSegment_025_0864_0027, g32p_row02_traceSegment_025_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 918 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 918 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 918 13 14, g32p_row02_traceSegment_025_0918_0013, g32p_row02_traceSegment_025_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 945 13 14, g32p_row02_traceSegment_025_0945_0013, g32p_row02_traceSegment_025_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 918 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 918 27 27, g32p_row02_traceSegment_025_0918_0027, g32p_row02_traceSegment_025_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 864 108 = [0, 0, 0, 6, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 864 54 54, g32p_row02_traceSegment_025_0864_0054, g32p_row02_traceSegment_025_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 972 13 14, g32p_row02_traceSegment_025_0972_0013, g32p_row02_traceSegment_025_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 999 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1012 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 999 27 = [0, 0, 0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 999 13 14, g32p_row02_traceSegment_025_0999_0013, g32p_row02_traceSegment_025_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 972 54 = [0, 0, 0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 972 27 27, g32p_row02_traceSegment_025_0972_0027, g32p_row02_traceSegment_025_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1026 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1039 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1026 27 = [0, 0, 0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1026 13 14, g32p_row02_traceSegment_025_1026_0013, g32p_row02_traceSegment_025_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1053 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1066 14 = [0, 0, 0, 2, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1053 27 = [0, 0, 0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1053 13 14, g32p_row02_traceSegment_025_1053_0013, g32p_row02_traceSegment_025_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1026 54 = [0, 0, 0, 6, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1026 27 27, g32p_row02_traceSegment_025_1026_0027, g32p_row02_traceSegment_025_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 972 108 = [0, 0, 0, 9, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 972 54 54, g32p_row02_traceSegment_025_0972_0054, g32p_row02_traceSegment_025_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 864 216 = [0, 0, 0, 15, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 864 108 108, g32p_row02_traceSegment_025_0864_0108, g32p_row02_traceSegment_025_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1080 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1093 14 = [0, 0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1080 27 = [0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1080 13 14, g32p_row02_traceSegment_025_1080_0013, g32p_row02_traceSegment_025_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1107 13 = [0, 0, 0, 2, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1120 14 = [0, 0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1107 27 = [0, 0, 0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1107 13 14, g32p_row02_traceSegment_025_1107_0013, g32p_row02_traceSegment_025_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1080 54 = [0, 0, 0, 5, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1080 27 27, g32p_row02_traceSegment_025_1080_0027, g32p_row02_traceSegment_025_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1134 13 14, g32p_row02_traceSegment_025_1134_0013, g32p_row02_traceSegment_025_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1161 13 14, g32p_row02_traceSegment_025_1161_0013, g32p_row02_traceSegment_025_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1134 27 27, g32p_row02_traceSegment_025_1134_0027, g32p_row02_traceSegment_025_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 1080 108 = [0, 0, 0, 5, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1080 54 54, g32p_row02_traceSegment_025_1080_0054, g32p_row02_traceSegment_025_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1188 13 14, g32p_row02_traceSegment_025_1188_0013, g32p_row02_traceSegment_025_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1215 13 14, g32p_row02_traceSegment_025_1215_0013, g32p_row02_traceSegment_025_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1188 27 27, g32p_row02_traceSegment_025_1188_0027, g32p_row02_traceSegment_025_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1242 13 14, g32p_row02_traceSegment_025_1242_0013, g32p_row02_traceSegment_025_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1269 13 14, g32p_row02_traceSegment_025_1269_0013, g32p_row02_traceSegment_025_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1242 27 27, g32p_row02_traceSegment_025_1242_0027, g32p_row02_traceSegment_025_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1188 54 54, g32p_row02_traceSegment_025_1188_0054, g32p_row02_traceSegment_025_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 1080 216 = [0, 0, 0, 5, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1080 108 108, g32p_row02_traceSegment_025_1080_0108, g32p_row02_traceSegment_025_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_025 864 432 = [0, 0, 0, 20, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 864 216 216, g32p_row02_traceSegment_025_0864_0216, g32p_row02_traceSegment_025_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1296 13 14, g32p_row02_traceSegment_025_1296_0013, g32p_row02_traceSegment_025_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1323 13 14, g32p_row02_traceSegment_025_1323_0013, g32p_row02_traceSegment_025_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1296 27 27, g32p_row02_traceSegment_025_1296_0027, g32p_row02_traceSegment_025_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1350 13 14, g32p_row02_traceSegment_025_1350_0013, g32p_row02_traceSegment_025_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1377 13 14, g32p_row02_traceSegment_025_1377_0013, g32p_row02_traceSegment_025_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1350 27 27, g32p_row02_traceSegment_025_1350_0027, g32p_row02_traceSegment_025_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1296 54 54, g32p_row02_traceSegment_025_1296_0054, g32p_row02_traceSegment_025_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1404 13 14, g32p_row02_traceSegment_025_1404_0013, g32p_row02_traceSegment_025_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1431 13 14, g32p_row02_traceSegment_025_1431_0013, g32p_row02_traceSegment_025_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1404 27 27, g32p_row02_traceSegment_025_1404_0027, g32p_row02_traceSegment_025_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1458 13 14, g32p_row02_traceSegment_025_1458_0013, g32p_row02_traceSegment_025_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1498 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1485 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1485 13 14, g32p_row02_traceSegment_025_1485_0013, g32p_row02_traceSegment_025_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1458 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1458 27 27, g32p_row02_traceSegment_025_1458_0027, g32p_row02_traceSegment_025_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 1404 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1404 54 54, g32p_row02_traceSegment_025_1404_0054, g32p_row02_traceSegment_025_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 1296 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1296 108 108, g32p_row02_traceSegment_025_1296_0108, g32p_row02_traceSegment_025_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1512 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1525 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1512 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1512 13 14, g32p_row02_traceSegment_025_1512_0013, g32p_row02_traceSegment_025_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1539 13 14, g32p_row02_traceSegment_025_1539_0013, g32p_row02_traceSegment_025_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1512 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1512 27 27, g32p_row02_traceSegment_025_1512_0027, g32p_row02_traceSegment_025_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1566 13 14, g32p_row02_traceSegment_025_1566_0013, g32p_row02_traceSegment_025_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1593 13 14, g32p_row02_traceSegment_025_1593_0013, g32p_row02_traceSegment_025_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1566 27 27, g32p_row02_traceSegment_025_1566_0027, g32p_row02_traceSegment_025_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 1512 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1512 54 54, g32p_row02_traceSegment_025_1512_0054, g32p_row02_traceSegment_025_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1620 13 14, g32p_row02_traceSegment_025_1620_0013, g32p_row02_traceSegment_025_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1647 13 14, g32p_row02_traceSegment_025_1647_0013, g32p_row02_traceSegment_025_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1620 27 27, g32p_row02_traceSegment_025_1620_0027, g32p_row02_traceSegment_025_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1674 13 14, g32p_row02_traceSegment_025_1674_0013, g32p_row02_traceSegment_025_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1701 13 14, g32p_row02_traceSegment_025_1701_0013, g32p_row02_traceSegment_025_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1674 27 27, g32p_row02_traceSegment_025_1674_0027, g32p_row02_traceSegment_025_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1620 54 54, g32p_row02_traceSegment_025_1620_0054, g32p_row02_traceSegment_025_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 1512 216 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1512 108 108, g32p_row02_traceSegment_025_1512_0108, g32p_row02_traceSegment_025_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_025 1296 432 = [0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1296 216 216, g32p_row02_traceSegment_025_1296_0216, g32p_row02_traceSegment_025_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_025 864 864 = [0, 0, 0, 22, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 864 432 432, g32p_row02_traceSegment_025_0864_0432, g32p_row02_traceSegment_025_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_025 0 1728 = [0, 0, 0, 56, 27] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 0 864 864, g32p_row02_traceSegment_025_0000_0864, g32p_row02_traceSegment_025_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1728 13 14, g32p_row02_traceSegment_025_1728_0013, g32p_row02_traceSegment_025_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1755 13 14, g32p_row02_traceSegment_025_1755_0013, g32p_row02_traceSegment_025_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1728 27 27, g32p_row02_traceSegment_025_1728_0027, g32p_row02_traceSegment_025_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1782 13 14, g32p_row02_traceSegment_025_1782_0013, g32p_row02_traceSegment_025_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1809 13 14, g32p_row02_traceSegment_025_1809_0013, g32p_row02_traceSegment_025_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1782 27 27, g32p_row02_traceSegment_025_1782_0027, g32p_row02_traceSegment_025_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1728 54 54, g32p_row02_traceSegment_025_1728_0054, g32p_row02_traceSegment_025_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1836 13 14, g32p_row02_traceSegment_025_1836_0013, g32p_row02_traceSegment_025_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1863 13 14, g32p_row02_traceSegment_025_1863_0013, g32p_row02_traceSegment_025_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1836 27 27, g32p_row02_traceSegment_025_1836_0027, g32p_row02_traceSegment_025_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1890 13 14, g32p_row02_traceSegment_025_1890_0013, g32p_row02_traceSegment_025_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1917 13 14, g32p_row02_traceSegment_025_1917_0013, g32p_row02_traceSegment_025_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1890 27 27, g32p_row02_traceSegment_025_1890_0027, g32p_row02_traceSegment_025_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1836 54 54, g32p_row02_traceSegment_025_1836_0054, g32p_row02_traceSegment_025_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1728 108 108, g32p_row02_traceSegment_025_1728_0108, g32p_row02_traceSegment_025_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1957 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1944 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1944 13 14, g32p_row02_traceSegment_025_1944_0013, g32p_row02_traceSegment_025_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1971 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 1984 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1971 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1971 13 14, g32p_row02_traceSegment_025_1971_0013, g32p_row02_traceSegment_025_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1944 54 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1944 27 27, g32p_row02_traceSegment_025_1944_0027, g32p_row02_traceSegment_025_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 1998 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 1998 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1998 13 14, g32p_row02_traceSegment_025_1998_0013, g32p_row02_traceSegment_025_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2025 13 14, g32p_row02_traceSegment_025_2025_0013, g32p_row02_traceSegment_025_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 1998 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1998 27 27, g32p_row02_traceSegment_025_1998_0027, g32p_row02_traceSegment_025_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 1944 108 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1944 54 54, g32p_row02_traceSegment_025_1944_0054, g32p_row02_traceSegment_025_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2065 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2052 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2052 13 14, g32p_row02_traceSegment_025_2052_0013, g32p_row02_traceSegment_025_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2079 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2079 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2079 13 14, g32p_row02_traceSegment_025_2079_0013, g32p_row02_traceSegment_025_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2052 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2052 27 27, g32p_row02_traceSegment_025_2052_0027, g32p_row02_traceSegment_025_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2106 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2119 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2106 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2106 13 14, g32p_row02_traceSegment_025_2106_0013, g32p_row02_traceSegment_025_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2146 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2133 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2133 13 14, g32p_row02_traceSegment_025_2133_0013, g32p_row02_traceSegment_025_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2106 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2106 27 27, g32p_row02_traceSegment_025_2106_0027, g32p_row02_traceSegment_025_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 2052 108 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2052 54 54, g32p_row02_traceSegment_025_2052_0054, g32p_row02_traceSegment_025_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 1944 216 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1944 108 108, g32p_row02_traceSegment_025_1944_0108, g32p_row02_traceSegment_025_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_025 1728 432 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1728 216 216, g32p_row02_traceSegment_025_1728_0216, g32p_row02_traceSegment_025_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2160 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2160 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2160 13 14, g32p_row02_traceSegment_025_2160_0013, g32p_row02_traceSegment_025_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2187 13 14, g32p_row02_traceSegment_025_2187_0013, g32p_row02_traceSegment_025_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2160 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2160 27 27, g32p_row02_traceSegment_025_2160_0027, g32p_row02_traceSegment_025_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2214 13 14, g32p_row02_traceSegment_025_2214_0013, g32p_row02_traceSegment_025_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2254 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2241 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2241 13 14, g32p_row02_traceSegment_025_2241_0013, g32p_row02_traceSegment_025_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2214 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2214 27 27, g32p_row02_traceSegment_025_2214_0027, g32p_row02_traceSegment_025_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 2160 108 = [0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2160 54 54, g32p_row02_traceSegment_025_2160_0054, g32p_row02_traceSegment_025_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2268 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2268 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2268 13 14, g32p_row02_traceSegment_025_2268_0013, g32p_row02_traceSegment_025_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2295 13 14, g32p_row02_traceSegment_025_2295_0013, g32p_row02_traceSegment_025_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2268 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2268 27 27, g32p_row02_traceSegment_025_2268_0027, g32p_row02_traceSegment_025_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2322 13 14, g32p_row02_traceSegment_025_2322_0013, g32p_row02_traceSegment_025_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2349 13 14, g32p_row02_traceSegment_025_2349_0013, g32p_row02_traceSegment_025_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2322 27 27, g32p_row02_traceSegment_025_2322_0027, g32p_row02_traceSegment_025_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 2268 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2268 54 54, g32p_row02_traceSegment_025_2268_0054, g32p_row02_traceSegment_025_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 2160 216 = [0, 0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2160 108 108, g32p_row02_traceSegment_025_2160_0108, g32p_row02_traceSegment_025_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2376 13 14, g32p_row02_traceSegment_025_2376_0013, g32p_row02_traceSegment_025_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2403 13 14, g32p_row02_traceSegment_025_2403_0013, g32p_row02_traceSegment_025_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2376 27 27, g32p_row02_traceSegment_025_2376_0027, g32p_row02_traceSegment_025_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2430 13 14, g32p_row02_traceSegment_025_2430_0013, g32p_row02_traceSegment_025_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2470 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2457 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2457 13 14, g32p_row02_traceSegment_025_2457_0013, g32p_row02_traceSegment_025_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2430 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2430 27 27, g32p_row02_traceSegment_025_2430_0027, g32p_row02_traceSegment_025_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 2376 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2376 54 54, g32p_row02_traceSegment_025_2376_0054, g32p_row02_traceSegment_025_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2484 13 14, g32p_row02_traceSegment_025_2484_0013, g32p_row02_traceSegment_025_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2511 13 14, g32p_row02_traceSegment_025_2511_0013, g32p_row02_traceSegment_025_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2484 27 27, g32p_row02_traceSegment_025_2484_0027, g32p_row02_traceSegment_025_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2551 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2538 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2538 13 14, g32p_row02_traceSegment_025_2538_0013, g32p_row02_traceSegment_025_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2565 13 14, g32p_row02_traceSegment_025_2565_0013, g32p_row02_traceSegment_025_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2538 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2538 27 27, g32p_row02_traceSegment_025_2538_0027, g32p_row02_traceSegment_025_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 2484 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2484 54 54, g32p_row02_traceSegment_025_2484_0054, g32p_row02_traceSegment_025_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 2376 216 = [0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2376 108 108, g32p_row02_traceSegment_025_2376_0108, g32p_row02_traceSegment_025_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_025 2160 432 = [0, 0, 0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2160 216 216, g32p_row02_traceSegment_025_2160_0216, g32p_row02_traceSegment_025_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_025 1728 864 = [0, 0, 0, 14, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1728 432 432, g32p_row02_traceSegment_025_1728_0432, g32p_row02_traceSegment_025_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2605 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2592 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2592 13 14, g32p_row02_traceSegment_025_2592_0013, g32p_row02_traceSegment_025_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2619 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2619 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2619 13 14, g32p_row02_traceSegment_025_2619_0013, g32p_row02_traceSegment_025_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2592 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2592 27 27, g32p_row02_traceSegment_025_2592_0027, g32p_row02_traceSegment_025_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2646 13 14, g32p_row02_traceSegment_025_2646_0013, g32p_row02_traceSegment_025_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2673 13 14, g32p_row02_traceSegment_025_2673_0013, g32p_row02_traceSegment_025_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2646 27 27, g32p_row02_traceSegment_025_2646_0027, g32p_row02_traceSegment_025_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 2592 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2592 54 54, g32p_row02_traceSegment_025_2592_0054, g32p_row02_traceSegment_025_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2700 13 14, g32p_row02_traceSegment_025_2700_0013, g32p_row02_traceSegment_025_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2727 13 14, g32p_row02_traceSegment_025_2727_0013, g32p_row02_traceSegment_025_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2700 27 27, g32p_row02_traceSegment_025_2700_0027, g32p_row02_traceSegment_025_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2754 13 14, g32p_row02_traceSegment_025_2754_0013, g32p_row02_traceSegment_025_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2781 13 14, g32p_row02_traceSegment_025_2781_0013, g32p_row02_traceSegment_025_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2754 27 27, g32p_row02_traceSegment_025_2754_0027, g32p_row02_traceSegment_025_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2700 54 54, g32p_row02_traceSegment_025_2700_0054, g32p_row02_traceSegment_025_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 2592 216 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2592 108 108, g32p_row02_traceSegment_025_2592_0108, g32p_row02_traceSegment_025_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2821 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2808 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2808 13 14, g32p_row02_traceSegment_025_2808_0013, g32p_row02_traceSegment_025_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2835 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2835 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2835 13 14, g32p_row02_traceSegment_025_2835_0013, g32p_row02_traceSegment_025_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2808 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2808 27 27, g32p_row02_traceSegment_025_2808_0027, g32p_row02_traceSegment_025_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2862 13 14, g32p_row02_traceSegment_025_2862_0013, g32p_row02_traceSegment_025_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2889 13 14, g32p_row02_traceSegment_025_2889_0013, g32p_row02_traceSegment_025_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2862 27 27, g32p_row02_traceSegment_025_2862_0027, g32p_row02_traceSegment_025_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 2808 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2808 54 54, g32p_row02_traceSegment_025_2808_0054, g32p_row02_traceSegment_025_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2916 13 14, g32p_row02_traceSegment_025_2916_0013, g32p_row02_traceSegment_025_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2943 13 14, g32p_row02_traceSegment_025_2943_0013, g32p_row02_traceSegment_025_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2916 27 27, g32p_row02_traceSegment_025_2916_0027, g32p_row02_traceSegment_025_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2970 13 = [0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 2983 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2970 27 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2970 13 14, g32p_row02_traceSegment_025_2970_0013, g32p_row02_traceSegment_025_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 2997 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3010 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 2997 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2997 13 14, g32p_row02_traceSegment_025_2997_0013, g32p_row02_traceSegment_025_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 2970 54 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2970 27 27, g32p_row02_traceSegment_025_2970_0027, g32p_row02_traceSegment_025_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 2916 108 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2916 54 54, g32p_row02_traceSegment_025_2916_0054, g32p_row02_traceSegment_025_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 2808 216 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2808 108 108, g32p_row02_traceSegment_025_2808_0108, g32p_row02_traceSegment_025_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_025 2592 432 = [0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2592 216 216, g32p_row02_traceSegment_025_2592_0216, g32p_row02_traceSegment_025_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3037 14 = [0, 0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3024 27 = [0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3024 13 14, g32p_row02_traceSegment_025_3024_0013, g32p_row02_traceSegment_025_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3064 14 = [0, 0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3051 27 = [0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3051 13 14, g32p_row02_traceSegment_025_3051_0013, g32p_row02_traceSegment_025_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 3024 54 = [0, 0, 0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3024 27 27, g32p_row02_traceSegment_025_3024_0027, g32p_row02_traceSegment_025_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3078 13 14, g32p_row02_traceSegment_025_3078_0013, g32p_row02_traceSegment_025_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3118 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3105 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3105 13 14, g32p_row02_traceSegment_025_3105_0013, g32p_row02_traceSegment_025_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 3078 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3078 27 27, g32p_row02_traceSegment_025_3078_0027, g32p_row02_traceSegment_025_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 3024 108 = [0, 0, 0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3024 54 54, g32p_row02_traceSegment_025_3024_0054, g32p_row02_traceSegment_025_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3132 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3145 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3132 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3132 13 14, g32p_row02_traceSegment_025_3132_0013, g32p_row02_traceSegment_025_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3159 13 14, g32p_row02_traceSegment_025_3159_0013, g32p_row02_traceSegment_025_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 3132 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3132 27 27, g32p_row02_traceSegment_025_3132_0027, g32p_row02_traceSegment_025_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3186 13 14, g32p_row02_traceSegment_025_3186_0013, g32p_row02_traceSegment_025_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3213 13 14, g32p_row02_traceSegment_025_3213_0013, g32p_row02_traceSegment_025_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3186 27 27, g32p_row02_traceSegment_025_3186_0027, g32p_row02_traceSegment_025_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 3132 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3132 54 54, g32p_row02_traceSegment_025_3132_0054, g32p_row02_traceSegment_025_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 3024 216 = [0, 0, 0, 8, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3024 108 108, g32p_row02_traceSegment_025_3024_0108, g32p_row02_traceSegment_025_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3240 13 14, g32p_row02_traceSegment_025_3240_0013, g32p_row02_traceSegment_025_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3267 13 14, g32p_row02_traceSegment_025_3267_0013, g32p_row02_traceSegment_025_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3240 27 27, g32p_row02_traceSegment_025_3240_0027, g32p_row02_traceSegment_025_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3294 13 14, g32p_row02_traceSegment_025_3294_0013, g32p_row02_traceSegment_025_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3321 13 14, g32p_row02_traceSegment_025_3321_0013, g32p_row02_traceSegment_025_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3294 27 27, g32p_row02_traceSegment_025_3294_0027, g32p_row02_traceSegment_025_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3240 54 54, g32p_row02_traceSegment_025_3240_0054, g32p_row02_traceSegment_025_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3348 13 14, g32p_row02_traceSegment_025_3348_0013, g32p_row02_traceSegment_025_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3375 13 14, g32p_row02_traceSegment_025_3375_0013, g32p_row02_traceSegment_025_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3348 27 27, g32p_row02_traceSegment_025_3348_0027, g32p_row02_traceSegment_025_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3402 13 14, g32p_row02_traceSegment_025_3402_0013, g32p_row02_traceSegment_025_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_025 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_025 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_025_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_025 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3429 13 14, g32p_row02_traceSegment_025_3429_0013, g32p_row02_traceSegment_025_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_025 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3402 27 27, g32p_row02_traceSegment_025_3402_0027, g32p_row02_traceSegment_025_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_025 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3348 54 54, g32p_row02_traceSegment_025_3348_0054, g32p_row02_traceSegment_025_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_025 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3240 108 108, g32p_row02_traceSegment_025_3240_0108, g32p_row02_traceSegment_025_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_025_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_025 3024 432 = [0, 0, 0, 8, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 3024 216 216, g32p_row02_traceSegment_025_3024_0216, g32p_row02_traceSegment_025_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_025_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_025 2592 864 = [0, 0, 0, 26, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 2592 432 432, g32p_row02_traceSegment_025_2592_0432, g32p_row02_traceSegment_025_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_025_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_025 1728 1728 = [0, 0, 0, 40, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 1728 864 864, g32p_row02_traceSegment_025_1728_0864, g32p_row02_traceSegment_025_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_025_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_025 0 3456 = [0, 0, 0, 96, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_025 0 1728 1728, g32p_row02_traceSegment_025_0000_1728, g32p_row02_traceSegment_025_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 25 = [0, 0, 0, 96, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_025_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_027 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 27 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_027_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 0 13 14, g32p_row02_traceSegment_027_0000_0013, g32p_row02_traceSegment_027_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 27 13 14, g32p_row02_traceSegment_027_0027_0013, g32p_row02_traceSegment_027_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 0 27 27, g32p_row02_traceSegment_027_0000_0027, g32p_row02_traceSegment_027_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 54 13 14, g32p_row02_traceSegment_027_0054_0013, g32p_row02_traceSegment_027_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 81 13 14, g32p_row02_traceSegment_027_0081_0013, g32p_row02_traceSegment_027_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 54 27 27, g32p_row02_traceSegment_027_0054_0027, g32p_row02_traceSegment_027_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 0 54 54, g32p_row02_traceSegment_027_0000_0054, g32p_row02_traceSegment_027_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 108 13 14, g32p_row02_traceSegment_027_0108_0013, g32p_row02_traceSegment_027_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 135 13 14, g32p_row02_traceSegment_027_0135_0013, g32p_row02_traceSegment_027_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 108 27 27, g32p_row02_traceSegment_027_0108_0027, g32p_row02_traceSegment_027_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 162 13 14, g32p_row02_traceSegment_027_0162_0013, g32p_row02_traceSegment_027_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 189 13 14, g32p_row02_traceSegment_027_0189_0013, g32p_row02_traceSegment_027_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 162 27 27, g32p_row02_traceSegment_027_0162_0027, g32p_row02_traceSegment_027_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 108 54 54, g32p_row02_traceSegment_027_0108_0054, g32p_row02_traceSegment_027_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 0 108 108, g32p_row02_traceSegment_027_0000_0108, g32p_row02_traceSegment_027_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 229 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 216 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 216 13 14, g32p_row02_traceSegment_027_0216_0013, g32p_row02_traceSegment_027_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 243 13 14, g32p_row02_traceSegment_027_0243_0013, g32p_row02_traceSegment_027_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 216 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 216 27 27, g32p_row02_traceSegment_027_0216_0027, g32p_row02_traceSegment_027_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 270 13 14, g32p_row02_traceSegment_027_0270_0013, g32p_row02_traceSegment_027_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 297 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 310 14 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 297 27 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 297 13 14, g32p_row02_traceSegment_027_0297_0013, g32p_row02_traceSegment_027_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 270 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 270 27 27, g32p_row02_traceSegment_027_0270_0027, g32p_row02_traceSegment_027_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 216 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 216 54 54, g32p_row02_traceSegment_027_0216_0054, g32p_row02_traceSegment_027_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 324 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 324 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 324 13 14, g32p_row02_traceSegment_027_0324_0013, g32p_row02_traceSegment_027_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 351 13 14, g32p_row02_traceSegment_027_0351_0013, g32p_row02_traceSegment_027_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 324 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 324 27 27, g32p_row02_traceSegment_027_0324_0027, g32p_row02_traceSegment_027_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 378 13 14, g32p_row02_traceSegment_027_0378_0013, g32p_row02_traceSegment_027_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 405 13 14, g32p_row02_traceSegment_027_0405_0013, g32p_row02_traceSegment_027_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 378 27 27, g32p_row02_traceSegment_027_0378_0027, g32p_row02_traceSegment_027_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 324 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 324 54 54, g32p_row02_traceSegment_027_0324_0054, g32p_row02_traceSegment_027_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 216 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 216 108 108, g32p_row02_traceSegment_027_0216_0108, g32p_row02_traceSegment_027_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_027 0 432 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 0 216 216, g32p_row02_traceSegment_027_0000_0216, g32p_row02_traceSegment_027_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 432 13 14, g32p_row02_traceSegment_027_0432_0013, g32p_row02_traceSegment_027_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 459 13 14, g32p_row02_traceSegment_027_0459_0013, g32p_row02_traceSegment_027_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 432 27 27, g32p_row02_traceSegment_027_0432_0027, g32p_row02_traceSegment_027_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 499 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 486 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 486 13 14, g32p_row02_traceSegment_027_0486_0013, g32p_row02_traceSegment_027_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 513 13 14, g32p_row02_traceSegment_027_0513_0013, g32p_row02_traceSegment_027_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 486 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 486 27 27, g32p_row02_traceSegment_027_0486_0027, g32p_row02_traceSegment_027_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 432 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 432 54 54, g32p_row02_traceSegment_027_0432_0054, g32p_row02_traceSegment_027_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 540 13 14, g32p_row02_traceSegment_027_0540_0013, g32p_row02_traceSegment_027_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 567 13 14, g32p_row02_traceSegment_027_0567_0013, g32p_row02_traceSegment_027_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 540 27 27, g32p_row02_traceSegment_027_0540_0027, g32p_row02_traceSegment_027_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 594 13 14, g32p_row02_traceSegment_027_0594_0013, g32p_row02_traceSegment_027_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 621 13 14, g32p_row02_traceSegment_027_0621_0013, g32p_row02_traceSegment_027_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 594 27 27, g32p_row02_traceSegment_027_0594_0027, g32p_row02_traceSegment_027_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 540 54 54, g32p_row02_traceSegment_027_0540_0054, g32p_row02_traceSegment_027_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 432 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 432 108 108, g32p_row02_traceSegment_027_0432_0108, g32p_row02_traceSegment_027_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 648 13 14, g32p_row02_traceSegment_027_0648_0013, g32p_row02_traceSegment_027_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 675 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 675 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 675 13 14, g32p_row02_traceSegment_027_0675_0013, g32p_row02_traceSegment_027_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 648 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 648 27 27, g32p_row02_traceSegment_027_0648_0027, g32p_row02_traceSegment_027_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 702 13 14, g32p_row02_traceSegment_027_0702_0013, g32p_row02_traceSegment_027_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 729 13 14, g32p_row02_traceSegment_027_0729_0013, g32p_row02_traceSegment_027_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 702 27 27, g32p_row02_traceSegment_027_0702_0027, g32p_row02_traceSegment_027_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 648 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 648 54 54, g32p_row02_traceSegment_027_0648_0054, g32p_row02_traceSegment_027_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 756 13 14, g32p_row02_traceSegment_027_0756_0013, g32p_row02_traceSegment_027_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 783 13 14, g32p_row02_traceSegment_027_0783_0013, g32p_row02_traceSegment_027_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 756 27 27, g32p_row02_traceSegment_027_0756_0027, g32p_row02_traceSegment_027_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 810 13 14, g32p_row02_traceSegment_027_0810_0013, g32p_row02_traceSegment_027_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 850 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 837 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 837 13 14, g32p_row02_traceSegment_027_0837_0013, g32p_row02_traceSegment_027_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 810 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 810 27 27, g32p_row02_traceSegment_027_0810_0027, g32p_row02_traceSegment_027_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 756 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 756 54 54, g32p_row02_traceSegment_027_0756_0054, g32p_row02_traceSegment_027_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 648 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 648 108 108, g32p_row02_traceSegment_027_0648_0108, g32p_row02_traceSegment_027_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_027 432 432 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 432 216 216, g32p_row02_traceSegment_027_0432_0216, g32p_row02_traceSegment_027_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_027 0 864 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 0 432 432, g32p_row02_traceSegment_027_0000_0432, g32p_row02_traceSegment_027_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 877 14 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 864 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 864 13 14, g32p_row02_traceSegment_027_0864_0013, g32p_row02_traceSegment_027_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 891 13 14, g32p_row02_traceSegment_027_0891_0013, g32p_row02_traceSegment_027_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 864 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 864 27 27, g32p_row02_traceSegment_027_0864_0027, g32p_row02_traceSegment_027_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 931 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 918 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 918 13 14, g32p_row02_traceSegment_027_0918_0013, g32p_row02_traceSegment_027_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 945 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 945 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 945 13 14, g32p_row02_traceSegment_027_0945_0013, g32p_row02_traceSegment_027_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 918 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 918 27 27, g32p_row02_traceSegment_027_0918_0027, g32p_row02_traceSegment_027_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 864 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 864 54 54, g32p_row02_traceSegment_027_0864_0054, g32p_row02_traceSegment_027_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 972 13 14, g32p_row02_traceSegment_027_0972_0013, g32p_row02_traceSegment_027_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 999 13 14, g32p_row02_traceSegment_027_0999_0013, g32p_row02_traceSegment_027_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 972 27 27, g32p_row02_traceSegment_027_0972_0027, g32p_row02_traceSegment_027_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1026 13 14, g32p_row02_traceSegment_027_1026_0013, g32p_row02_traceSegment_027_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1053 13 14, g32p_row02_traceSegment_027_1053_0013, g32p_row02_traceSegment_027_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1026 27 27, g32p_row02_traceSegment_027_1026_0027, g32p_row02_traceSegment_027_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 972 54 54, g32p_row02_traceSegment_027_0972_0054, g32p_row02_traceSegment_027_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 864 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 864 108 108, g32p_row02_traceSegment_027_0864_0108, g32p_row02_traceSegment_027_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1080 13 14, g32p_row02_traceSegment_027_1080_0013, g32p_row02_traceSegment_027_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1107 13 14, g32p_row02_traceSegment_027_1107_0013, g32p_row02_traceSegment_027_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1080 27 27, g32p_row02_traceSegment_027_1080_0027, g32p_row02_traceSegment_027_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1134 13 14, g32p_row02_traceSegment_027_1134_0013, g32p_row02_traceSegment_027_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1161 13 14, g32p_row02_traceSegment_027_1161_0013, g32p_row02_traceSegment_027_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1134 27 27, g32p_row02_traceSegment_027_1134_0027, g32p_row02_traceSegment_027_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1080 54 54, g32p_row02_traceSegment_027_1080_0054, g32p_row02_traceSegment_027_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1188 13 14, g32p_row02_traceSegment_027_1188_0013, g32p_row02_traceSegment_027_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1215 13 14, g32p_row02_traceSegment_027_1215_0013, g32p_row02_traceSegment_027_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1188 27 27, g32p_row02_traceSegment_027_1188_0027, g32p_row02_traceSegment_027_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1255 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1242 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1242 13 14, g32p_row02_traceSegment_027_1242_0013, g32p_row02_traceSegment_027_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1269 13 14, g32p_row02_traceSegment_027_1269_0013, g32p_row02_traceSegment_027_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1242 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1242 27 27, g32p_row02_traceSegment_027_1242_0027, g32p_row02_traceSegment_027_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 1188 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1188 54 54, g32p_row02_traceSegment_027_1188_0054, g32p_row02_traceSegment_027_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 1080 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1080 108 108, g32p_row02_traceSegment_027_1080_0108, g32p_row02_traceSegment_027_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_027 864 432 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 864 216 216, g32p_row02_traceSegment_027_0864_0216, g32p_row02_traceSegment_027_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1296 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1296 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1296 13 14, g32p_row02_traceSegment_027_1296_0013, g32p_row02_traceSegment_027_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1323 13 14, g32p_row02_traceSegment_027_1323_0013, g32p_row02_traceSegment_027_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1296 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1296 27 27, g32p_row02_traceSegment_027_1296_0027, g32p_row02_traceSegment_027_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1350 13 14, g32p_row02_traceSegment_027_1350_0013, g32p_row02_traceSegment_027_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1377 13 14, g32p_row02_traceSegment_027_1377_0013, g32p_row02_traceSegment_027_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1350 27 27, g32p_row02_traceSegment_027_1350_0027, g32p_row02_traceSegment_027_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 1296 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1296 54 54, g32p_row02_traceSegment_027_1296_0054, g32p_row02_traceSegment_027_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1404 13 14, g32p_row02_traceSegment_027_1404_0013, g32p_row02_traceSegment_027_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1431 13 14, g32p_row02_traceSegment_027_1431_0013, g32p_row02_traceSegment_027_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1404 27 27, g32p_row02_traceSegment_027_1404_0027, g32p_row02_traceSegment_027_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1458 13 14, g32p_row02_traceSegment_027_1458_0013, g32p_row02_traceSegment_027_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1485 13 14, g32p_row02_traceSegment_027_1485_0013, g32p_row02_traceSegment_027_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1458 27 27, g32p_row02_traceSegment_027_1458_0027, g32p_row02_traceSegment_027_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1404 54 54, g32p_row02_traceSegment_027_1404_0054, g32p_row02_traceSegment_027_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 1296 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1296 108 108, g32p_row02_traceSegment_027_1296_0108, g32p_row02_traceSegment_027_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1512 13 14, g32p_row02_traceSegment_027_1512_0013, g32p_row02_traceSegment_027_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1539 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1552 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1539 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1539 13 14, g32p_row02_traceSegment_027_1539_0013, g32p_row02_traceSegment_027_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1512 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1512 27 27, g32p_row02_traceSegment_027_1512_0027, g32p_row02_traceSegment_027_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1579 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1566 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1566 13 14, g32p_row02_traceSegment_027_1566_0013, g32p_row02_traceSegment_027_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1593 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1606 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1593 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1593 13 14, g32p_row02_traceSegment_027_1593_0013, g32p_row02_traceSegment_027_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1566 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1566 27 27, g32p_row02_traceSegment_027_1566_0027, g32p_row02_traceSegment_027_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 1512 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1512 54 54, g32p_row02_traceSegment_027_1512_0054, g32p_row02_traceSegment_027_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1620 13 14, g32p_row02_traceSegment_027_1620_0013, g32p_row02_traceSegment_027_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1647 13 14, g32p_row02_traceSegment_027_1647_0013, g32p_row02_traceSegment_027_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1620 27 27, g32p_row02_traceSegment_027_1620_0027, g32p_row02_traceSegment_027_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1674 13 14, g32p_row02_traceSegment_027_1674_0013, g32p_row02_traceSegment_027_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1701 13 14, g32p_row02_traceSegment_027_1701_0013, g32p_row02_traceSegment_027_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1674 27 27, g32p_row02_traceSegment_027_1674_0027, g32p_row02_traceSegment_027_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1620 54 54, g32p_row02_traceSegment_027_1620_0054, g32p_row02_traceSegment_027_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 1512 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1512 108 108, g32p_row02_traceSegment_027_1512_0108, g32p_row02_traceSegment_027_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_027 1296 432 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1296 216 216, g32p_row02_traceSegment_027_1296_0216, g32p_row02_traceSegment_027_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_027 864 864 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 864 432 432, g32p_row02_traceSegment_027_0864_0432, g32p_row02_traceSegment_027_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_027 0 1728 = [0, 0, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 0 864 864, g32p_row02_traceSegment_027_0000_0864, g32p_row02_traceSegment_027_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1741 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1728 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1728 13 14, g32p_row02_traceSegment_027_1728_0013, g32p_row02_traceSegment_027_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1755 13 14, g32p_row02_traceSegment_027_1755_0013, g32p_row02_traceSegment_027_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1728 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1728 27 27, g32p_row02_traceSegment_027_1728_0027, g32p_row02_traceSegment_027_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1782 13 14, g32p_row02_traceSegment_027_1782_0013, g32p_row02_traceSegment_027_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1809 13 14, g32p_row02_traceSegment_027_1809_0013, g32p_row02_traceSegment_027_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1782 27 27, g32p_row02_traceSegment_027_1782_0027, g32p_row02_traceSegment_027_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 1728 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1728 54 54, g32p_row02_traceSegment_027_1728_0054, g32p_row02_traceSegment_027_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1836 13 14, g32p_row02_traceSegment_027_1836_0013, g32p_row02_traceSegment_027_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1863 13 14, g32p_row02_traceSegment_027_1863_0013, g32p_row02_traceSegment_027_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1836 27 27, g32p_row02_traceSegment_027_1836_0027, g32p_row02_traceSegment_027_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1890 13 14, g32p_row02_traceSegment_027_1890_0013, g32p_row02_traceSegment_027_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1917 13 14, g32p_row02_traceSegment_027_1917_0013, g32p_row02_traceSegment_027_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1890 27 27, g32p_row02_traceSegment_027_1890_0027, g32p_row02_traceSegment_027_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1836 54 54, g32p_row02_traceSegment_027_1836_0054, g32p_row02_traceSegment_027_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 1728 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1728 108 108, g32p_row02_traceSegment_027_1728_0108, g32p_row02_traceSegment_027_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1944 13 14, g32p_row02_traceSegment_027_1944_0013, g32p_row02_traceSegment_027_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1971 13 14, g32p_row02_traceSegment_027_1971_0013, g32p_row02_traceSegment_027_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1944 27 27, g32p_row02_traceSegment_027_1944_0027, g32p_row02_traceSegment_027_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1998 13 14, g32p_row02_traceSegment_027_1998_0013, g32p_row02_traceSegment_027_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2038 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2025 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2025 13 14, g32p_row02_traceSegment_027_2025_0013, g32p_row02_traceSegment_027_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 1998 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1998 27 27, g32p_row02_traceSegment_027_1998_0027, g32p_row02_traceSegment_027_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 1944 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1944 54 54, g32p_row02_traceSegment_027_1944_0054, g32p_row02_traceSegment_027_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2052 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2065 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2052 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2052 13 14, g32p_row02_traceSegment_027_2052_0013, g32p_row02_traceSegment_027_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2079 13 14, g32p_row02_traceSegment_027_2079_0013, g32p_row02_traceSegment_027_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2052 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2052 27 27, g32p_row02_traceSegment_027_2052_0027, g32p_row02_traceSegment_027_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2106 13 14, g32p_row02_traceSegment_027_2106_0013, g32p_row02_traceSegment_027_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2133 13 14, g32p_row02_traceSegment_027_2133_0013, g32p_row02_traceSegment_027_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2106 27 27, g32p_row02_traceSegment_027_2106_0027, g32p_row02_traceSegment_027_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 2052 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2052 54 54, g32p_row02_traceSegment_027_2052_0054, g32p_row02_traceSegment_027_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 1944 216 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1944 108 108, g32p_row02_traceSegment_027_1944_0108, g32p_row02_traceSegment_027_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_027 1728 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1728 216 216, g32p_row02_traceSegment_027_1728_0216, g32p_row02_traceSegment_027_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2160 13 14, g32p_row02_traceSegment_027_2160_0013, g32p_row02_traceSegment_027_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2187 13 14, g32p_row02_traceSegment_027_2187_0013, g32p_row02_traceSegment_027_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2160 27 27, g32p_row02_traceSegment_027_2160_0027, g32p_row02_traceSegment_027_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2214 13 14, g32p_row02_traceSegment_027_2214_0013, g32p_row02_traceSegment_027_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2241 13 14, g32p_row02_traceSegment_027_2241_0013, g32p_row02_traceSegment_027_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2214 27 27, g32p_row02_traceSegment_027_2214_0027, g32p_row02_traceSegment_027_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2160 54 54, g32p_row02_traceSegment_027_2160_0054, g32p_row02_traceSegment_027_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2268 13 14, g32p_row02_traceSegment_027_2268_0013, g32p_row02_traceSegment_027_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2295 13 14, g32p_row02_traceSegment_027_2295_0013, g32p_row02_traceSegment_027_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2268 27 27, g32p_row02_traceSegment_027_2268_0027, g32p_row02_traceSegment_027_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2322 13 14, g32p_row02_traceSegment_027_2322_0013, g32p_row02_traceSegment_027_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2349 13 14, g32p_row02_traceSegment_027_2349_0013, g32p_row02_traceSegment_027_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2322 27 27, g32p_row02_traceSegment_027_2322_0027, g32p_row02_traceSegment_027_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2268 54 54, g32p_row02_traceSegment_027_2268_0054, g32p_row02_traceSegment_027_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2160 108 108, g32p_row02_traceSegment_027_2160_0108, g32p_row02_traceSegment_027_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2376 13 14, g32p_row02_traceSegment_027_2376_0013, g32p_row02_traceSegment_027_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2403 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2416 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2403 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2403 13 14, g32p_row02_traceSegment_027_2403_0013, g32p_row02_traceSegment_027_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2376 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2376 27 27, g32p_row02_traceSegment_027_2376_0027, g32p_row02_traceSegment_027_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2430 13 14, g32p_row02_traceSegment_027_2430_0013, g32p_row02_traceSegment_027_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2457 13 14, g32p_row02_traceSegment_027_2457_0013, g32p_row02_traceSegment_027_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2430 27 27, g32p_row02_traceSegment_027_2430_0027, g32p_row02_traceSegment_027_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 2376 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2376 54 54, g32p_row02_traceSegment_027_2376_0054, g32p_row02_traceSegment_027_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2484 13 14, g32p_row02_traceSegment_027_2484_0013, g32p_row02_traceSegment_027_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2511 13 14, g32p_row02_traceSegment_027_2511_0013, g32p_row02_traceSegment_027_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2484 27 27, g32p_row02_traceSegment_027_2484_0027, g32p_row02_traceSegment_027_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2538 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2551 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2538 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2538 13 14, g32p_row02_traceSegment_027_2538_0013, g32p_row02_traceSegment_027_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2565 13 14, g32p_row02_traceSegment_027_2565_0013, g32p_row02_traceSegment_027_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2538 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2538 27 27, g32p_row02_traceSegment_027_2538_0027, g32p_row02_traceSegment_027_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 2484 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2484 54 54, g32p_row02_traceSegment_027_2484_0054, g32p_row02_traceSegment_027_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 2376 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2376 108 108, g32p_row02_traceSegment_027_2376_0108, g32p_row02_traceSegment_027_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_027 2160 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2160 216 216, g32p_row02_traceSegment_027_2160_0216, g32p_row02_traceSegment_027_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_027 1728 864 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1728 432 432, g32p_row02_traceSegment_027_1728_0432, g32p_row02_traceSegment_027_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2592 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2605 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2592 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2592 13 14, g32p_row02_traceSegment_027_2592_0013, g32p_row02_traceSegment_027_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2619 13 14, g32p_row02_traceSegment_027_2619_0013, g32p_row02_traceSegment_027_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2592 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2592 27 27, g32p_row02_traceSegment_027_2592_0027, g32p_row02_traceSegment_027_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2646 13 14, g32p_row02_traceSegment_027_2646_0013, g32p_row02_traceSegment_027_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2673 13 14, g32p_row02_traceSegment_027_2673_0013, g32p_row02_traceSegment_027_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2646 27 27, g32p_row02_traceSegment_027_2646_0027, g32p_row02_traceSegment_027_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 2592 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2592 54 54, g32p_row02_traceSegment_027_2592_0054, g32p_row02_traceSegment_027_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2700 13 14, g32p_row02_traceSegment_027_2700_0013, g32p_row02_traceSegment_027_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2727 13 14, g32p_row02_traceSegment_027_2727_0013, g32p_row02_traceSegment_027_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2700 27 27, g32p_row02_traceSegment_027_2700_0027, g32p_row02_traceSegment_027_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2754 13 14, g32p_row02_traceSegment_027_2754_0013, g32p_row02_traceSegment_027_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2781 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2794 14 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2781 27 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2781 13 14, g32p_row02_traceSegment_027_2781_0013, g32p_row02_traceSegment_027_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2754 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2754 27 27, g32p_row02_traceSegment_027_2754_0027, g32p_row02_traceSegment_027_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 2700 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2700 54 54, g32p_row02_traceSegment_027_2700_0054, g32p_row02_traceSegment_027_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 2592 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2592 108 108, g32p_row02_traceSegment_027_2592_0108, g32p_row02_traceSegment_027_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2821 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2808 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2808 13 14, g32p_row02_traceSegment_027_2808_0013, g32p_row02_traceSegment_027_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2848 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2835 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2835 13 14, g32p_row02_traceSegment_027_2835_0013, g32p_row02_traceSegment_027_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2808 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2808 27 27, g32p_row02_traceSegment_027_2808_0027, g32p_row02_traceSegment_027_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2875 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2862 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2862 13 14, g32p_row02_traceSegment_027_2862_0013, g32p_row02_traceSegment_027_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2902 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2889 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2889 13 14, g32p_row02_traceSegment_027_2889_0013, g32p_row02_traceSegment_027_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2862 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2862 27 27, g32p_row02_traceSegment_027_2862_0027, g32p_row02_traceSegment_027_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 2808 108 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2808 54 54, g32p_row02_traceSegment_027_2808_0054, g32p_row02_traceSegment_027_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2916 13 14, g32p_row02_traceSegment_027_2916_0013, g32p_row02_traceSegment_027_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2956 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2943 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2943 13 14, g32p_row02_traceSegment_027_2943_0013, g32p_row02_traceSegment_027_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2916 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2916 27 27, g32p_row02_traceSegment_027_2916_0027, g32p_row02_traceSegment_027_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 2983 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2970 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2970 13 14, g32p_row02_traceSegment_027_2970_0013, g32p_row02_traceSegment_027_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2997 13 14, g32p_row02_traceSegment_027_2997_0013, g32p_row02_traceSegment_027_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 2970 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2970 27 27, g32p_row02_traceSegment_027_2970_0027, g32p_row02_traceSegment_027_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 2916 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2916 54 54, g32p_row02_traceSegment_027_2916_0054, g32p_row02_traceSegment_027_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 2808 216 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2808 108 108, g32p_row02_traceSegment_027_2808_0108, g32p_row02_traceSegment_027_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_027 2592 432 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2592 216 216, g32p_row02_traceSegment_027_2592_0216, g32p_row02_traceSegment_027_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3024 13 14, g32p_row02_traceSegment_027_3024_0013, g32p_row02_traceSegment_027_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3051 13 14, g32p_row02_traceSegment_027_3051_0013, g32p_row02_traceSegment_027_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3024 27 27, g32p_row02_traceSegment_027_3024_0027, g32p_row02_traceSegment_027_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3078 13 14, g32p_row02_traceSegment_027_3078_0013, g32p_row02_traceSegment_027_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3105 13 14, g32p_row02_traceSegment_027_3105_0013, g32p_row02_traceSegment_027_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3078 27 27, g32p_row02_traceSegment_027_3078_0027, g32p_row02_traceSegment_027_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3024 54 54, g32p_row02_traceSegment_027_3024_0054, g32p_row02_traceSegment_027_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3132 13 14, g32p_row02_traceSegment_027_3132_0013, g32p_row02_traceSegment_027_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3172 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3159 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3159 13 14, g32p_row02_traceSegment_027_3159_0013, g32p_row02_traceSegment_027_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 3132 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3132 27 27, g32p_row02_traceSegment_027_3132_0027, g32p_row02_traceSegment_027_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3199 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3186 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3186 13 14, g32p_row02_traceSegment_027_3186_0013, g32p_row02_traceSegment_027_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3213 13 14, g32p_row02_traceSegment_027_3213_0013, g32p_row02_traceSegment_027_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 3186 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3186 27 27, g32p_row02_traceSegment_027_3186_0027, g32p_row02_traceSegment_027_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 3132 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3132 54 54, g32p_row02_traceSegment_027_3132_0054, g32p_row02_traceSegment_027_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 3024 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3024 108 108, g32p_row02_traceSegment_027_3024_0108, g32p_row02_traceSegment_027_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3240 13 14, g32p_row02_traceSegment_027_3240_0013, g32p_row02_traceSegment_027_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3267 13 14, g32p_row02_traceSegment_027_3267_0013, g32p_row02_traceSegment_027_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3240 27 27, g32p_row02_traceSegment_027_3240_0027, g32p_row02_traceSegment_027_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3294 13 14, g32p_row02_traceSegment_027_3294_0013, g32p_row02_traceSegment_027_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3321 13 14, g32p_row02_traceSegment_027_3321_0013, g32p_row02_traceSegment_027_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3294 27 27, g32p_row02_traceSegment_027_3294_0027, g32p_row02_traceSegment_027_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3240 54 54, g32p_row02_traceSegment_027_3240_0054, g32p_row02_traceSegment_027_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3361 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3348 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3348 13 14, g32p_row02_traceSegment_027_3348_0013, g32p_row02_traceSegment_027_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3375 13 14, g32p_row02_traceSegment_027_3375_0013, g32p_row02_traceSegment_027_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 3348 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3348 27 27, g32p_row02_traceSegment_027_3348_0027, g32p_row02_traceSegment_027_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3402 13 14, g32p_row02_traceSegment_027_3402_0013, g32p_row02_traceSegment_027_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_027 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_027 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_027_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_027 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3429 13 14, g32p_row02_traceSegment_027_3429_0013, g32p_row02_traceSegment_027_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_027 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3402 27 27, g32p_row02_traceSegment_027_3402_0027, g32p_row02_traceSegment_027_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_027 3348 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3348 54 54, g32p_row02_traceSegment_027_3348_0054, g32p_row02_traceSegment_027_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_027 3240 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3240 108 108, g32p_row02_traceSegment_027_3240_0108, g32p_row02_traceSegment_027_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_027_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_027 3024 432 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 3024 216 216, g32p_row02_traceSegment_027_3024_0216, g32p_row02_traceSegment_027_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_027_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_027 2592 864 = [0, 0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 2592 432 432, g32p_row02_traceSegment_027_2592_0432, g32p_row02_traceSegment_027_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_027_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_027 1728 1728 = [0, 0, 0, 0, 27] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 1728 864 864, g32p_row02_traceSegment_027_1728_0864, g32p_row02_traceSegment_027_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_027_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_027 0 3456 = [0, 0, 0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_027 0 1728 1728, g32p_row02_traceSegment_027_0000_1728, g32p_row02_traceSegment_027_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_027 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 27 = [0, 0, 0, 0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_027_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_028 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 28 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_028_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 0 13 14, g32p_row02_traceSegment_028_0000_0013, g32p_row02_traceSegment_028_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 27 13 14, g32p_row02_traceSegment_028_0027_0013, g32p_row02_traceSegment_028_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 0 27 27, g32p_row02_traceSegment_028_0000_0027, g32p_row02_traceSegment_028_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 54 13 14, g32p_row02_traceSegment_028_0054_0013, g32p_row02_traceSegment_028_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 81 13 14, g32p_row02_traceSegment_028_0081_0013, g32p_row02_traceSegment_028_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 54 27 27, g32p_row02_traceSegment_028_0054_0027, g32p_row02_traceSegment_028_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 0 54 54, g32p_row02_traceSegment_028_0000_0054, g32p_row02_traceSegment_028_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 108 13 14, g32p_row02_traceSegment_028_0108_0013, g32p_row02_traceSegment_028_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 135 13 14, g32p_row02_traceSegment_028_0135_0013, g32p_row02_traceSegment_028_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 108 27 27, g32p_row02_traceSegment_028_0108_0027, g32p_row02_traceSegment_028_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 162 13 14, g32p_row02_traceSegment_028_0162_0013, g32p_row02_traceSegment_028_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 189 13 14, g32p_row02_traceSegment_028_0189_0013, g32p_row02_traceSegment_028_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 162 27 27, g32p_row02_traceSegment_028_0162_0027, g32p_row02_traceSegment_028_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 108 54 54, g32p_row02_traceSegment_028_0108_0054, g32p_row02_traceSegment_028_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 0 108 108, g32p_row02_traceSegment_028_0000_0108, g32p_row02_traceSegment_028_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 216 13 14, g32p_row02_traceSegment_028_0216_0013, g32p_row02_traceSegment_028_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 243 13 14, g32p_row02_traceSegment_028_0243_0013, g32p_row02_traceSegment_028_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 216 27 27, g32p_row02_traceSegment_028_0216_0027, g32p_row02_traceSegment_028_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 270 13 14, g32p_row02_traceSegment_028_0270_0013, g32p_row02_traceSegment_028_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 297 13 14, g32p_row02_traceSegment_028_0297_0013, g32p_row02_traceSegment_028_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 270 27 27, g32p_row02_traceSegment_028_0270_0027, g32p_row02_traceSegment_028_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 216 54 54, g32p_row02_traceSegment_028_0216_0054, g32p_row02_traceSegment_028_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 324 13 14, g32p_row02_traceSegment_028_0324_0013, g32p_row02_traceSegment_028_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 351 13 14, g32p_row02_traceSegment_028_0351_0013, g32p_row02_traceSegment_028_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 324 27 27, g32p_row02_traceSegment_028_0324_0027, g32p_row02_traceSegment_028_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 378 13 14, g32p_row02_traceSegment_028_0378_0013, g32p_row02_traceSegment_028_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 405 13 14, g32p_row02_traceSegment_028_0405_0013, g32p_row02_traceSegment_028_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 378 27 27, g32p_row02_traceSegment_028_0378_0027, g32p_row02_traceSegment_028_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 324 54 54, g32p_row02_traceSegment_028_0324_0054, g32p_row02_traceSegment_028_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 216 108 108, g32p_row02_traceSegment_028_0216_0108, g32p_row02_traceSegment_028_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_028 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 0 216 216, g32p_row02_traceSegment_028_0000_0216, g32p_row02_traceSegment_028_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 445 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 432 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 432 13 14, g32p_row02_traceSegment_028_0432_0013, g32p_row02_traceSegment_028_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 459 13 14, g32p_row02_traceSegment_028_0459_0013, g32p_row02_traceSegment_028_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 432 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 432 27 27, g32p_row02_traceSegment_028_0432_0027, g32p_row02_traceSegment_028_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 486 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 499 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 486 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 486 13 14, g32p_row02_traceSegment_028_0486_0013, g32p_row02_traceSegment_028_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 513 13 14, g32p_row02_traceSegment_028_0513_0013, g32p_row02_traceSegment_028_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 486 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 486 27 27, g32p_row02_traceSegment_028_0486_0027, g32p_row02_traceSegment_028_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 432 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 432 54 54, g32p_row02_traceSegment_028_0432_0054, g32p_row02_traceSegment_028_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 540 13 14, g32p_row02_traceSegment_028_0540_0013, g32p_row02_traceSegment_028_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 567 13 14, g32p_row02_traceSegment_028_0567_0013, g32p_row02_traceSegment_028_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 540 27 27, g32p_row02_traceSegment_028_0540_0027, g32p_row02_traceSegment_028_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 594 13 14, g32p_row02_traceSegment_028_0594_0013, g32p_row02_traceSegment_028_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 621 13 14, g32p_row02_traceSegment_028_0621_0013, g32p_row02_traceSegment_028_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 594 27 27, g32p_row02_traceSegment_028_0594_0027, g32p_row02_traceSegment_028_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 540 54 54, g32p_row02_traceSegment_028_0540_0054, g32p_row02_traceSegment_028_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 432 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 432 108 108, g32p_row02_traceSegment_028_0432_0108, g32p_row02_traceSegment_028_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 648 13 14, g32p_row02_traceSegment_028_0648_0013, g32p_row02_traceSegment_028_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 675 13 14, g32p_row02_traceSegment_028_0675_0013, g32p_row02_traceSegment_028_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 648 27 27, g32p_row02_traceSegment_028_0648_0027, g32p_row02_traceSegment_028_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 702 13 14, g32p_row02_traceSegment_028_0702_0013, g32p_row02_traceSegment_028_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 729 13 14, g32p_row02_traceSegment_028_0729_0013, g32p_row02_traceSegment_028_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 702 27 27, g32p_row02_traceSegment_028_0702_0027, g32p_row02_traceSegment_028_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 648 54 54, g32p_row02_traceSegment_028_0648_0054, g32p_row02_traceSegment_028_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 756 13 14, g32p_row02_traceSegment_028_0756_0013, g32p_row02_traceSegment_028_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 783 13 14, g32p_row02_traceSegment_028_0783_0013, g32p_row02_traceSegment_028_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 756 27 27, g32p_row02_traceSegment_028_0756_0027, g32p_row02_traceSegment_028_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 810 13 14, g32p_row02_traceSegment_028_0810_0013, g32p_row02_traceSegment_028_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 837 13 14, g32p_row02_traceSegment_028_0837_0013, g32p_row02_traceSegment_028_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 810 27 27, g32p_row02_traceSegment_028_0810_0027, g32p_row02_traceSegment_028_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 756 54 54, g32p_row02_traceSegment_028_0756_0054, g32p_row02_traceSegment_028_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 648 108 108, g32p_row02_traceSegment_028_0648_0108, g32p_row02_traceSegment_028_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_028 432 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 432 216 216, g32p_row02_traceSegment_028_0432_0216, g32p_row02_traceSegment_028_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_028 0 864 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 0 432 432, g32p_row02_traceSegment_028_0000_0432, g32p_row02_traceSegment_028_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 864 13 14, g32p_row02_traceSegment_028_0864_0013, g32p_row02_traceSegment_028_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 891 13 14, g32p_row02_traceSegment_028_0891_0013, g32p_row02_traceSegment_028_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 864 27 27, g32p_row02_traceSegment_028_0864_0027, g32p_row02_traceSegment_028_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 918 13 14, g32p_row02_traceSegment_028_0918_0013, g32p_row02_traceSegment_028_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 945 13 14, g32p_row02_traceSegment_028_0945_0013, g32p_row02_traceSegment_028_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 918 27 27, g32p_row02_traceSegment_028_0918_0027, g32p_row02_traceSegment_028_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 864 54 54, g32p_row02_traceSegment_028_0864_0054, g32p_row02_traceSegment_028_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 985 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 972 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 972 13 14, g32p_row02_traceSegment_028_0972_0013, g32p_row02_traceSegment_028_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 999 13 14, g32p_row02_traceSegment_028_0999_0013, g32p_row02_traceSegment_028_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 972 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 972 27 27, g32p_row02_traceSegment_028_0972_0027, g32p_row02_traceSegment_028_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1026 13 14, g32p_row02_traceSegment_028_1026_0013, g32p_row02_traceSegment_028_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1053 13 14, g32p_row02_traceSegment_028_1053_0013, g32p_row02_traceSegment_028_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1026 27 27, g32p_row02_traceSegment_028_1026_0027, g32p_row02_traceSegment_028_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 972 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 972 54 54, g32p_row02_traceSegment_028_0972_0054, g32p_row02_traceSegment_028_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 864 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 864 108 108, g32p_row02_traceSegment_028_0864_0108, g32p_row02_traceSegment_028_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1080 13 14, g32p_row02_traceSegment_028_1080_0013, g32p_row02_traceSegment_028_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1107 13 14, g32p_row02_traceSegment_028_1107_0013, g32p_row02_traceSegment_028_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1080 27 27, g32p_row02_traceSegment_028_1080_0027, g32p_row02_traceSegment_028_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1134 13 14, g32p_row02_traceSegment_028_1134_0013, g32p_row02_traceSegment_028_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1161 13 14, g32p_row02_traceSegment_028_1161_0013, g32p_row02_traceSegment_028_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1134 27 27, g32p_row02_traceSegment_028_1134_0027, g32p_row02_traceSegment_028_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1080 54 54, g32p_row02_traceSegment_028_1080_0054, g32p_row02_traceSegment_028_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1188 13 14, g32p_row02_traceSegment_028_1188_0013, g32p_row02_traceSegment_028_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1215 13 14, g32p_row02_traceSegment_028_1215_0013, g32p_row02_traceSegment_028_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1188 27 27, g32p_row02_traceSegment_028_1188_0027, g32p_row02_traceSegment_028_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1255 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1242 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1242 13 14, g32p_row02_traceSegment_028_1242_0013, g32p_row02_traceSegment_028_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1269 13 14, g32p_row02_traceSegment_028_1269_0013, g32p_row02_traceSegment_028_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1242 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1242 27 27, g32p_row02_traceSegment_028_1242_0027, g32p_row02_traceSegment_028_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 1188 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1188 54 54, g32p_row02_traceSegment_028_1188_0054, g32p_row02_traceSegment_028_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 1080 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1080 108 108, g32p_row02_traceSegment_028_1080_0108, g32p_row02_traceSegment_028_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_028 864 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 864 216 216, g32p_row02_traceSegment_028_0864_0216, g32p_row02_traceSegment_028_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1296 13 14, g32p_row02_traceSegment_028_1296_0013, g32p_row02_traceSegment_028_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1323 13 14, g32p_row02_traceSegment_028_1323_0013, g32p_row02_traceSegment_028_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1296 27 27, g32p_row02_traceSegment_028_1296_0027, g32p_row02_traceSegment_028_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1350 13 14, g32p_row02_traceSegment_028_1350_0013, g32p_row02_traceSegment_028_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1377 13 14, g32p_row02_traceSegment_028_1377_0013, g32p_row02_traceSegment_028_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1350 27 27, g32p_row02_traceSegment_028_1350_0027, g32p_row02_traceSegment_028_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1296 54 54, g32p_row02_traceSegment_028_1296_0054, g32p_row02_traceSegment_028_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1404 13 14, g32p_row02_traceSegment_028_1404_0013, g32p_row02_traceSegment_028_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1431 13 14, g32p_row02_traceSegment_028_1431_0013, g32p_row02_traceSegment_028_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1404 27 27, g32p_row02_traceSegment_028_1404_0027, g32p_row02_traceSegment_028_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1458 13 14, g32p_row02_traceSegment_028_1458_0013, g32p_row02_traceSegment_028_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1485 13 14, g32p_row02_traceSegment_028_1485_0013, g32p_row02_traceSegment_028_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1458 27 27, g32p_row02_traceSegment_028_1458_0027, g32p_row02_traceSegment_028_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1404 54 54, g32p_row02_traceSegment_028_1404_0054, g32p_row02_traceSegment_028_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1296 108 108, g32p_row02_traceSegment_028_1296_0108, g32p_row02_traceSegment_028_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1512 13 14, g32p_row02_traceSegment_028_1512_0013, g32p_row02_traceSegment_028_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1539 13 14, g32p_row02_traceSegment_028_1539_0013, g32p_row02_traceSegment_028_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1512 27 27, g32p_row02_traceSegment_028_1512_0027, g32p_row02_traceSegment_028_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1566 13 14, g32p_row02_traceSegment_028_1566_0013, g32p_row02_traceSegment_028_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1593 13 14, g32p_row02_traceSegment_028_1593_0013, g32p_row02_traceSegment_028_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1566 27 27, g32p_row02_traceSegment_028_1566_0027, g32p_row02_traceSegment_028_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1512 54 54, g32p_row02_traceSegment_028_1512_0054, g32p_row02_traceSegment_028_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1620 13 14, g32p_row02_traceSegment_028_1620_0013, g32p_row02_traceSegment_028_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1647 13 14, g32p_row02_traceSegment_028_1647_0013, g32p_row02_traceSegment_028_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1620 27 27, g32p_row02_traceSegment_028_1620_0027, g32p_row02_traceSegment_028_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1674 13 14, g32p_row02_traceSegment_028_1674_0013, g32p_row02_traceSegment_028_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1701 13 14, g32p_row02_traceSegment_028_1701_0013, g32p_row02_traceSegment_028_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1674 27 27, g32p_row02_traceSegment_028_1674_0027, g32p_row02_traceSegment_028_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1620 54 54, g32p_row02_traceSegment_028_1620_0054, g32p_row02_traceSegment_028_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1512 108 108, g32p_row02_traceSegment_028_1512_0108, g32p_row02_traceSegment_028_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_028 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1296 216 216, g32p_row02_traceSegment_028_1296_0216, g32p_row02_traceSegment_028_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_028 864 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 864 432 432, g32p_row02_traceSegment_028_0864_0432, g32p_row02_traceSegment_028_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_028 0 1728 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 0 864 864, g32p_row02_traceSegment_028_0000_0864, g32p_row02_traceSegment_028_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1728 13 14, g32p_row02_traceSegment_028_1728_0013, g32p_row02_traceSegment_028_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1755 13 14, g32p_row02_traceSegment_028_1755_0013, g32p_row02_traceSegment_028_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1728 27 27, g32p_row02_traceSegment_028_1728_0027, g32p_row02_traceSegment_028_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1782 13 14, g32p_row02_traceSegment_028_1782_0013, g32p_row02_traceSegment_028_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1809 13 14, g32p_row02_traceSegment_028_1809_0013, g32p_row02_traceSegment_028_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1782 27 27, g32p_row02_traceSegment_028_1782_0027, g32p_row02_traceSegment_028_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1728 54 54, g32p_row02_traceSegment_028_1728_0054, g32p_row02_traceSegment_028_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1836 13 14, g32p_row02_traceSegment_028_1836_0013, g32p_row02_traceSegment_028_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1863 13 14, g32p_row02_traceSegment_028_1863_0013, g32p_row02_traceSegment_028_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1836 27 27, g32p_row02_traceSegment_028_1836_0027, g32p_row02_traceSegment_028_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1890 13 14, g32p_row02_traceSegment_028_1890_0013, g32p_row02_traceSegment_028_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1917 13 14, g32p_row02_traceSegment_028_1917_0013, g32p_row02_traceSegment_028_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1890 27 27, g32p_row02_traceSegment_028_1890_0027, g32p_row02_traceSegment_028_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1836 54 54, g32p_row02_traceSegment_028_1836_0054, g32p_row02_traceSegment_028_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1728 108 108, g32p_row02_traceSegment_028_1728_0108, g32p_row02_traceSegment_028_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1944 13 14, g32p_row02_traceSegment_028_1944_0013, g32p_row02_traceSegment_028_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1971 13 14, g32p_row02_traceSegment_028_1971_0013, g32p_row02_traceSegment_028_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1944 27 27, g32p_row02_traceSegment_028_1944_0027, g32p_row02_traceSegment_028_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1998 13 14, g32p_row02_traceSegment_028_1998_0013, g32p_row02_traceSegment_028_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2025 13 14, g32p_row02_traceSegment_028_2025_0013, g32p_row02_traceSegment_028_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1998 27 27, g32p_row02_traceSegment_028_1998_0027, g32p_row02_traceSegment_028_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1944 54 54, g32p_row02_traceSegment_028_1944_0054, g32p_row02_traceSegment_028_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2052 13 14, g32p_row02_traceSegment_028_2052_0013, g32p_row02_traceSegment_028_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2079 13 14, g32p_row02_traceSegment_028_2079_0013, g32p_row02_traceSegment_028_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2052 27 27, g32p_row02_traceSegment_028_2052_0027, g32p_row02_traceSegment_028_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2106 13 14, g32p_row02_traceSegment_028_2106_0013, g32p_row02_traceSegment_028_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2133 13 14, g32p_row02_traceSegment_028_2133_0013, g32p_row02_traceSegment_028_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2106 27 27, g32p_row02_traceSegment_028_2106_0027, g32p_row02_traceSegment_028_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2052 54 54, g32p_row02_traceSegment_028_2052_0054, g32p_row02_traceSegment_028_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1944 108 108, g32p_row02_traceSegment_028_1944_0108, g32p_row02_traceSegment_028_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_028 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1728 216 216, g32p_row02_traceSegment_028_1728_0216, g32p_row02_traceSegment_028_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2160 13 14, g32p_row02_traceSegment_028_2160_0013, g32p_row02_traceSegment_028_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2187 13 14, g32p_row02_traceSegment_028_2187_0013, g32p_row02_traceSegment_028_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2160 27 27, g32p_row02_traceSegment_028_2160_0027, g32p_row02_traceSegment_028_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2214 13 14, g32p_row02_traceSegment_028_2214_0013, g32p_row02_traceSegment_028_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2241 13 14, g32p_row02_traceSegment_028_2241_0013, g32p_row02_traceSegment_028_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2214 27 27, g32p_row02_traceSegment_028_2214_0027, g32p_row02_traceSegment_028_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2160 54 54, g32p_row02_traceSegment_028_2160_0054, g32p_row02_traceSegment_028_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2268 13 14, g32p_row02_traceSegment_028_2268_0013, g32p_row02_traceSegment_028_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2295 13 14, g32p_row02_traceSegment_028_2295_0013, g32p_row02_traceSegment_028_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2268 27 27, g32p_row02_traceSegment_028_2268_0027, g32p_row02_traceSegment_028_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2322 13 14, g32p_row02_traceSegment_028_2322_0013, g32p_row02_traceSegment_028_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2349 13 14, g32p_row02_traceSegment_028_2349_0013, g32p_row02_traceSegment_028_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2322 27 27, g32p_row02_traceSegment_028_2322_0027, g32p_row02_traceSegment_028_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2268 54 54, g32p_row02_traceSegment_028_2268_0054, g32p_row02_traceSegment_028_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2160 108 108, g32p_row02_traceSegment_028_2160_0108, g32p_row02_traceSegment_028_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2389 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2376 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2376 13 14, g32p_row02_traceSegment_028_2376_0013, g32p_row02_traceSegment_028_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2403 13 14, g32p_row02_traceSegment_028_2403_0013, g32p_row02_traceSegment_028_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2376 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2376 27 27, g32p_row02_traceSegment_028_2376_0027, g32p_row02_traceSegment_028_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2443 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2430 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2430 13 14, g32p_row02_traceSegment_028_2430_0013, g32p_row02_traceSegment_028_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2457 13 14, g32p_row02_traceSegment_028_2457_0013, g32p_row02_traceSegment_028_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2430 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2430 27 27, g32p_row02_traceSegment_028_2430_0027, g32p_row02_traceSegment_028_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 2376 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2376 54 54, g32p_row02_traceSegment_028_2376_0054, g32p_row02_traceSegment_028_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2484 13 14, g32p_row02_traceSegment_028_2484_0013, g32p_row02_traceSegment_028_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2511 13 14, g32p_row02_traceSegment_028_2511_0013, g32p_row02_traceSegment_028_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2484 27 27, g32p_row02_traceSegment_028_2484_0027, g32p_row02_traceSegment_028_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2538 13 14, g32p_row02_traceSegment_028_2538_0013, g32p_row02_traceSegment_028_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2565 13 14, g32p_row02_traceSegment_028_2565_0013, g32p_row02_traceSegment_028_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2538 27 27, g32p_row02_traceSegment_028_2538_0027, g32p_row02_traceSegment_028_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2484 54 54, g32p_row02_traceSegment_028_2484_0054, g32p_row02_traceSegment_028_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 2376 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2376 108 108, g32p_row02_traceSegment_028_2376_0108, g32p_row02_traceSegment_028_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_028 2160 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2160 216 216, g32p_row02_traceSegment_028_2160_0216, g32p_row02_traceSegment_028_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_028 1728 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1728 432 432, g32p_row02_traceSegment_028_1728_0432, g32p_row02_traceSegment_028_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2592 13 14, g32p_row02_traceSegment_028_2592_0013, g32p_row02_traceSegment_028_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2619 13 14, g32p_row02_traceSegment_028_2619_0013, g32p_row02_traceSegment_028_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2592 27 27, g32p_row02_traceSegment_028_2592_0027, g32p_row02_traceSegment_028_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2646 13 14, g32p_row02_traceSegment_028_2646_0013, g32p_row02_traceSegment_028_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2673 13 14, g32p_row02_traceSegment_028_2673_0013, g32p_row02_traceSegment_028_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2646 27 27, g32p_row02_traceSegment_028_2646_0027, g32p_row02_traceSegment_028_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2592 54 54, g32p_row02_traceSegment_028_2592_0054, g32p_row02_traceSegment_028_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2700 13 14, g32p_row02_traceSegment_028_2700_0013, g32p_row02_traceSegment_028_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2727 13 14, g32p_row02_traceSegment_028_2727_0013, g32p_row02_traceSegment_028_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2700 27 27, g32p_row02_traceSegment_028_2700_0027, g32p_row02_traceSegment_028_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2754 13 14, g32p_row02_traceSegment_028_2754_0013, g32p_row02_traceSegment_028_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2781 13 14, g32p_row02_traceSegment_028_2781_0013, g32p_row02_traceSegment_028_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2754 27 27, g32p_row02_traceSegment_028_2754_0027, g32p_row02_traceSegment_028_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2700 54 54, g32p_row02_traceSegment_028_2700_0054, g32p_row02_traceSegment_028_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2592 108 108, g32p_row02_traceSegment_028_2592_0108, g32p_row02_traceSegment_028_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2808 13 14, g32p_row02_traceSegment_028_2808_0013, g32p_row02_traceSegment_028_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2835 13 14, g32p_row02_traceSegment_028_2835_0013, g32p_row02_traceSegment_028_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2808 27 27, g32p_row02_traceSegment_028_2808_0027, g32p_row02_traceSegment_028_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2862 13 14, g32p_row02_traceSegment_028_2862_0013, g32p_row02_traceSegment_028_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2889 13 14, g32p_row02_traceSegment_028_2889_0013, g32p_row02_traceSegment_028_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2862 27 27, g32p_row02_traceSegment_028_2862_0027, g32p_row02_traceSegment_028_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2808 54 54, g32p_row02_traceSegment_028_2808_0054, g32p_row02_traceSegment_028_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2916 13 14, g32p_row02_traceSegment_028_2916_0013, g32p_row02_traceSegment_028_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2943 13 14, g32p_row02_traceSegment_028_2943_0013, g32p_row02_traceSegment_028_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2916 27 27, g32p_row02_traceSegment_028_2916_0027, g32p_row02_traceSegment_028_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2970 13 14, g32p_row02_traceSegment_028_2970_0013, g32p_row02_traceSegment_028_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2997 13 14, g32p_row02_traceSegment_028_2997_0013, g32p_row02_traceSegment_028_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2970 27 27, g32p_row02_traceSegment_028_2970_0027, g32p_row02_traceSegment_028_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2916 54 54, g32p_row02_traceSegment_028_2916_0054, g32p_row02_traceSegment_028_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2808 108 108, g32p_row02_traceSegment_028_2808_0108, g32p_row02_traceSegment_028_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_028 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2592 216 216, g32p_row02_traceSegment_028_2592_0216, g32p_row02_traceSegment_028_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3024 13 14, g32p_row02_traceSegment_028_3024_0013, g32p_row02_traceSegment_028_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3051 13 14, g32p_row02_traceSegment_028_3051_0013, g32p_row02_traceSegment_028_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3024 27 27, g32p_row02_traceSegment_028_3024_0027, g32p_row02_traceSegment_028_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3078 13 14, g32p_row02_traceSegment_028_3078_0013, g32p_row02_traceSegment_028_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3105 13 14, g32p_row02_traceSegment_028_3105_0013, g32p_row02_traceSegment_028_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3078 27 27, g32p_row02_traceSegment_028_3078_0027, g32p_row02_traceSegment_028_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3024 54 54, g32p_row02_traceSegment_028_3024_0054, g32p_row02_traceSegment_028_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3132 13 14, g32p_row02_traceSegment_028_3132_0013, g32p_row02_traceSegment_028_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3159 13 14, g32p_row02_traceSegment_028_3159_0013, g32p_row02_traceSegment_028_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3132 27 27, g32p_row02_traceSegment_028_3132_0027, g32p_row02_traceSegment_028_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3186 13 14, g32p_row02_traceSegment_028_3186_0013, g32p_row02_traceSegment_028_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3213 13 14, g32p_row02_traceSegment_028_3213_0013, g32p_row02_traceSegment_028_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3186 27 27, g32p_row02_traceSegment_028_3186_0027, g32p_row02_traceSegment_028_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3132 54 54, g32p_row02_traceSegment_028_3132_0054, g32p_row02_traceSegment_028_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3024 108 108, g32p_row02_traceSegment_028_3024_0108, g32p_row02_traceSegment_028_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3240 13 14, g32p_row02_traceSegment_028_3240_0013, g32p_row02_traceSegment_028_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3267 13 14, g32p_row02_traceSegment_028_3267_0013, g32p_row02_traceSegment_028_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3240 27 27, g32p_row02_traceSegment_028_3240_0027, g32p_row02_traceSegment_028_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3294 13 14, g32p_row02_traceSegment_028_3294_0013, g32p_row02_traceSegment_028_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3321 13 14, g32p_row02_traceSegment_028_3321_0013, g32p_row02_traceSegment_028_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3294 27 27, g32p_row02_traceSegment_028_3294_0027, g32p_row02_traceSegment_028_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3240 54 54, g32p_row02_traceSegment_028_3240_0054, g32p_row02_traceSegment_028_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3348 13 14, g32p_row02_traceSegment_028_3348_0013, g32p_row02_traceSegment_028_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3375 13 14, g32p_row02_traceSegment_028_3375_0013, g32p_row02_traceSegment_028_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3348 27 27, g32p_row02_traceSegment_028_3348_0027, g32p_row02_traceSegment_028_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3402 13 14, g32p_row02_traceSegment_028_3402_0013, g32p_row02_traceSegment_028_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_028 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_028 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_028_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_028 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3429 13 14, g32p_row02_traceSegment_028_3429_0013, g32p_row02_traceSegment_028_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_028 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3402 27 27, g32p_row02_traceSegment_028_3402_0027, g32p_row02_traceSegment_028_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_028 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3348 54 54, g32p_row02_traceSegment_028_3348_0054, g32p_row02_traceSegment_028_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_028 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3240 108 108, g32p_row02_traceSegment_028_3240_0108, g32p_row02_traceSegment_028_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_028_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_028 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 3024 216 216, g32p_row02_traceSegment_028_3024_0216, g32p_row02_traceSegment_028_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_028_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_028 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 2592 432 432, g32p_row02_traceSegment_028_2592_0432, g32p_row02_traceSegment_028_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_028_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_028 1728 1728 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 1728 864 864, g32p_row02_traceSegment_028_1728_0864, g32p_row02_traceSegment_028_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_028_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_028 0 3456 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_028 0 1728 1728, g32p_row02_traceSegment_028_0000_1728, g32p_row02_traceSegment_028_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 28 = [0, 0, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_028_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_029 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 29 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_029_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 0 13 14, g32p_row02_traceSegment_029_0000_0013, g32p_row02_traceSegment_029_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 27 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 40 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 27 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 27 13 14, g32p_row02_traceSegment_029_0027_0013, g32p_row02_traceSegment_029_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 0 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 0 27 27, g32p_row02_traceSegment_029_0000_0027, g32p_row02_traceSegment_029_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 54 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 54 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 54 13 14, g32p_row02_traceSegment_029_0054_0013, g32p_row02_traceSegment_029_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 81 13 14, g32p_row02_traceSegment_029_0081_0013, g32p_row02_traceSegment_029_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 54 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 54 27 27, g32p_row02_traceSegment_029_0054_0027, g32p_row02_traceSegment_029_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 0 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 0 54 54, g32p_row02_traceSegment_029_0000_0054, g32p_row02_traceSegment_029_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 108 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 121 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 108 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 108 13 14, g32p_row02_traceSegment_029_0108_0013, g32p_row02_traceSegment_029_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 135 13 14, g32p_row02_traceSegment_029_0135_0013, g32p_row02_traceSegment_029_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 108 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 108 27 27, g32p_row02_traceSegment_029_0108_0027, g32p_row02_traceSegment_029_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 162 13 14, g32p_row02_traceSegment_029_0162_0013, g32p_row02_traceSegment_029_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 189 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 202 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 189 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 189 13 14, g32p_row02_traceSegment_029_0189_0013, g32p_row02_traceSegment_029_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 162 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 162 27 27, g32p_row02_traceSegment_029_0162_0027, g32p_row02_traceSegment_029_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 108 108 = [0, 0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 108 54 54, g32p_row02_traceSegment_029_0108_0054, g32p_row02_traceSegment_029_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 0 216 = [0, 0, 6, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 0 108 108, g32p_row02_traceSegment_029_0000_0108, g32p_row02_traceSegment_029_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 229 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 216 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 216 13 14, g32p_row02_traceSegment_029_0216_0013, g32p_row02_traceSegment_029_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 243 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 243 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 243 13 14, g32p_row02_traceSegment_029_0243_0013, g32p_row02_traceSegment_029_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 216 54 = [0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 216 27 27, g32p_row02_traceSegment_029_0216_0027, g32p_row02_traceSegment_029_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 270 13 14, g32p_row02_traceSegment_029_0270_0013, g32p_row02_traceSegment_029_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 297 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 310 14 = [0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 297 27 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 297 13 14, g32p_row02_traceSegment_029_0297_0013, g32p_row02_traceSegment_029_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 270 54 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 270 27 27, g32p_row02_traceSegment_029_0270_0027, g32p_row02_traceSegment_029_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 216 108 = [0, 0, 1, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 216 54 54, g32p_row02_traceSegment_029_0216_0054, g32p_row02_traceSegment_029_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 324 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 324 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 324 13 14, g32p_row02_traceSegment_029_0324_0013, g32p_row02_traceSegment_029_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 364 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 351 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 351 13 14, g32p_row02_traceSegment_029_0351_0013, g32p_row02_traceSegment_029_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 324 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 324 27 27, g32p_row02_traceSegment_029_0324_0027, g32p_row02_traceSegment_029_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 378 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 391 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 378 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 378 13 14, g32p_row02_traceSegment_029_0378_0013, g32p_row02_traceSegment_029_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 405 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 405 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 405 13 14, g32p_row02_traceSegment_029_0405_0013, g32p_row02_traceSegment_029_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 378 54 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 378 27 27, g32p_row02_traceSegment_029_0378_0027, g32p_row02_traceSegment_029_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 324 108 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 324 54 54, g32p_row02_traceSegment_029_0324_0054, g32p_row02_traceSegment_029_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 216 216 = [0, 0, 1, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 216 108 108, g32p_row02_traceSegment_029_0216_0108, g32p_row02_traceSegment_029_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_029 0 432 = [0, 0, 7, 23] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 0 216 216, g32p_row02_traceSegment_029_0000_0216, g32p_row02_traceSegment_029_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 445 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 432 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 432 13 14, g32p_row02_traceSegment_029_0432_0013, g32p_row02_traceSegment_029_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 472 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 459 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 459 13 14, g32p_row02_traceSegment_029_0459_0013, g32p_row02_traceSegment_029_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 432 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 432 27 27, g32p_row02_traceSegment_029_0432_0027, g32p_row02_traceSegment_029_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 486 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 499 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 486 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 486 13 14, g32p_row02_traceSegment_029_0486_0013, g32p_row02_traceSegment_029_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 513 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 513 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 513 13 14, g32p_row02_traceSegment_029_0513_0013, g32p_row02_traceSegment_029_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 486 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 486 27 27, g32p_row02_traceSegment_029_0486_0027, g32p_row02_traceSegment_029_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 432 108 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 432 54 54, g32p_row02_traceSegment_029_0432_0054, g32p_row02_traceSegment_029_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 553 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 540 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 540 13 14, g32p_row02_traceSegment_029_0540_0013, g32p_row02_traceSegment_029_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 567 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 580 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 567 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 567 13 14, g32p_row02_traceSegment_029_0567_0013, g32p_row02_traceSegment_029_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 540 54 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 540 27 27, g32p_row02_traceSegment_029_0540_0027, g32p_row02_traceSegment_029_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 594 13 14, g32p_row02_traceSegment_029_0594_0013, g32p_row02_traceSegment_029_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 621 13 14, g32p_row02_traceSegment_029_0621_0013, g32p_row02_traceSegment_029_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 594 27 27, g32p_row02_traceSegment_029_0594_0027, g32p_row02_traceSegment_029_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 540 108 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 540 54 54, g32p_row02_traceSegment_029_0540_0054, g32p_row02_traceSegment_029_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 432 216 = [0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 432 108 108, g32p_row02_traceSegment_029_0432_0108, g32p_row02_traceSegment_029_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 648 13 14, g32p_row02_traceSegment_029_0648_0013, g32p_row02_traceSegment_029_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 675 13 14, g32p_row02_traceSegment_029_0675_0013, g32p_row02_traceSegment_029_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 648 27 27, g32p_row02_traceSegment_029_0648_0027, g32p_row02_traceSegment_029_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 715 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 702 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 702 13 14, g32p_row02_traceSegment_029_0702_0013, g32p_row02_traceSegment_029_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 742 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 729 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 729 13 14, g32p_row02_traceSegment_029_0729_0013, g32p_row02_traceSegment_029_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 702 54 = [0, 0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 702 27 27, g32p_row02_traceSegment_029_0702_0027, g32p_row02_traceSegment_029_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 648 108 = [0, 0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 648 54 54, g32p_row02_traceSegment_029_0648_0054, g32p_row02_traceSegment_029_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 756 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 769 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 756 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 756 13 14, g32p_row02_traceSegment_029_0756_0013, g32p_row02_traceSegment_029_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 796 14 = [0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 783 27 = [0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 783 13 14, g32p_row02_traceSegment_029_0783_0013, g32p_row02_traceSegment_029_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 756 54 = [0, 0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 756 27 27, g32p_row02_traceSegment_029_0756_0027, g32p_row02_traceSegment_029_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 810 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 823 14 = [0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 810 27 = [0, 0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 810 13 14, g32p_row02_traceSegment_029_0810_0013, g32p_row02_traceSegment_029_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 837 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 837 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 837 13 14, g32p_row02_traceSegment_029_0837_0013, g32p_row02_traceSegment_029_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 810 54 = [0, 0, 1, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 810 27 27, g32p_row02_traceSegment_029_0810_0027, g32p_row02_traceSegment_029_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 756 108 = [0, 0, 4, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 756 54 54, g32p_row02_traceSegment_029_0756_0054, g32p_row02_traceSegment_029_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 648 216 = [0, 0, 6, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 648 108 108, g32p_row02_traceSegment_029_0648_0108, g32p_row02_traceSegment_029_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_029 432 432 = [0, 0, 6, 25] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 432 216 216, g32p_row02_traceSegment_029_0432_0216, g32p_row02_traceSegment_029_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_029 0 864 = [0, 0, 13, 48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 0 432 432, g32p_row02_traceSegment_029_0000_0432, g32p_row02_traceSegment_029_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 864 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 864 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 864 13 14, g32p_row02_traceSegment_029_0864_0013, g32p_row02_traceSegment_029_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 891 13 14, g32p_row02_traceSegment_029_0891_0013, g32p_row02_traceSegment_029_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 864 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 864 27 27, g32p_row02_traceSegment_029_0864_0027, g32p_row02_traceSegment_029_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 918 13 14, g32p_row02_traceSegment_029_0918_0013, g32p_row02_traceSegment_029_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 945 13 14, g32p_row02_traceSegment_029_0945_0013, g32p_row02_traceSegment_029_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 918 27 27, g32p_row02_traceSegment_029_0918_0027, g32p_row02_traceSegment_029_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 864 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 864 54 54, g32p_row02_traceSegment_029_0864_0054, g32p_row02_traceSegment_029_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 985 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 972 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 972 13 14, g32p_row02_traceSegment_029_0972_0013, g32p_row02_traceSegment_029_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 999 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1012 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 999 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 999 13 14, g32p_row02_traceSegment_029_0999_0013, g32p_row02_traceSegment_029_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 972 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 972 27 27, g32p_row02_traceSegment_029_0972_0027, g32p_row02_traceSegment_029_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1026 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1039 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1026 27 = [0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1026 13 14, g32p_row02_traceSegment_029_1026_0013, g32p_row02_traceSegment_029_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1053 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1053 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1053 13 14, g32p_row02_traceSegment_029_1053_0013, g32p_row02_traceSegment_029_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1026 54 = [0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1026 27 27, g32p_row02_traceSegment_029_1026_0027, g32p_row02_traceSegment_029_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 972 108 = [0, 0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 972 54 54, g32p_row02_traceSegment_029_0972_0054, g32p_row02_traceSegment_029_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 864 216 = [0, 0, 3, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 864 108 108, g32p_row02_traceSegment_029_0864_0108, g32p_row02_traceSegment_029_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1093 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1080 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1080 13 14, g32p_row02_traceSegment_029_1080_0013, g32p_row02_traceSegment_029_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1107 13 = [0, 0, 1, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1120 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1107 27 = [0, 0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1107 13 14, g32p_row02_traceSegment_029_1107_0013, g32p_row02_traceSegment_029_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1080 54 = [0, 0, 1, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1080 27 27, g32p_row02_traceSegment_029_1080_0027, g32p_row02_traceSegment_029_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1134 13 14, g32p_row02_traceSegment_029_1134_0013, g32p_row02_traceSegment_029_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1161 13 14, g32p_row02_traceSegment_029_1161_0013, g32p_row02_traceSegment_029_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1134 27 27, g32p_row02_traceSegment_029_1134_0027, g32p_row02_traceSegment_029_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 1080 108 = [0, 0, 1, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1080 54 54, g32p_row02_traceSegment_029_1080_0054, g32p_row02_traceSegment_029_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1188 13 14, g32p_row02_traceSegment_029_1188_0013, g32p_row02_traceSegment_029_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1215 13 14, g32p_row02_traceSegment_029_1215_0013, g32p_row02_traceSegment_029_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1188 27 27, g32p_row02_traceSegment_029_1188_0027, g32p_row02_traceSegment_029_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1242 13 14, g32p_row02_traceSegment_029_1242_0013, g32p_row02_traceSegment_029_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1269 13 14, g32p_row02_traceSegment_029_1269_0013, g32p_row02_traceSegment_029_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1242 27 27, g32p_row02_traceSegment_029_1242_0027, g32p_row02_traceSegment_029_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1188 54 54, g32p_row02_traceSegment_029_1188_0054, g32p_row02_traceSegment_029_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 1080 216 = [0, 0, 1, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1080 108 108, g32p_row02_traceSegment_029_1080_0108, g32p_row02_traceSegment_029_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_029 864 432 = [0, 0, 4, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 864 216 216, g32p_row02_traceSegment_029_0864_0216, g32p_row02_traceSegment_029_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1296 13 14, g32p_row02_traceSegment_029_1296_0013, g32p_row02_traceSegment_029_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1336 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1323 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1323 13 14, g32p_row02_traceSegment_029_1323_0013, g32p_row02_traceSegment_029_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1296 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1296 27 27, g32p_row02_traceSegment_029_1296_0027, g32p_row02_traceSegment_029_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1363 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1350 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1350 13 14, g32p_row02_traceSegment_029_1350_0013, g32p_row02_traceSegment_029_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1377 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1377 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1377 13 14, g32p_row02_traceSegment_029_1377_0013, g32p_row02_traceSegment_029_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1350 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1350 27 27, g32p_row02_traceSegment_029_1350_0027, g32p_row02_traceSegment_029_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 1296 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1296 54 54, g32p_row02_traceSegment_029_1296_0054, g32p_row02_traceSegment_029_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1417 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1404 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1404 13 14, g32p_row02_traceSegment_029_1404_0013, g32p_row02_traceSegment_029_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1431 13 14, g32p_row02_traceSegment_029_1431_0013, g32p_row02_traceSegment_029_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1404 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1404 27 27, g32p_row02_traceSegment_029_1404_0027, g32p_row02_traceSegment_029_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1458 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1471 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1458 27 = [0, 0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1458 13 14, g32p_row02_traceSegment_029_1458_0013, g32p_row02_traceSegment_029_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1485 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1498 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1485 27 = [0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1485 13 14, g32p_row02_traceSegment_029_1485_0013, g32p_row02_traceSegment_029_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1458 54 = [0, 0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1458 27 27, g32p_row02_traceSegment_029_1458_0027, g32p_row02_traceSegment_029_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 1404 108 = [0, 0, 5, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1404 54 54, g32p_row02_traceSegment_029_1404_0054, g32p_row02_traceSegment_029_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 1296 216 = [0, 0, 8, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1296 108 108, g32p_row02_traceSegment_029_1296_0108, g32p_row02_traceSegment_029_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1525 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1512 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1512 13 14, g32p_row02_traceSegment_029_1512_0013, g32p_row02_traceSegment_029_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1539 13 14, g32p_row02_traceSegment_029_1539_0013, g32p_row02_traceSegment_029_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1512 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1512 27 27, g32p_row02_traceSegment_029_1512_0027, g32p_row02_traceSegment_029_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1566 13 14, g32p_row02_traceSegment_029_1566_0013, g32p_row02_traceSegment_029_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1593 13 14, g32p_row02_traceSegment_029_1593_0013, g32p_row02_traceSegment_029_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1566 27 27, g32p_row02_traceSegment_029_1566_0027, g32p_row02_traceSegment_029_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 1512 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1512 54 54, g32p_row02_traceSegment_029_1512_0054, g32p_row02_traceSegment_029_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1633 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1620 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1620 13 14, g32p_row02_traceSegment_029_1620_0013, g32p_row02_traceSegment_029_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1647 13 14, g32p_row02_traceSegment_029_1647_0013, g32p_row02_traceSegment_029_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1620 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1620 27 27, g32p_row02_traceSegment_029_1620_0027, g32p_row02_traceSegment_029_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1674 13 14, g32p_row02_traceSegment_029_1674_0013, g32p_row02_traceSegment_029_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1701 13 14, g32p_row02_traceSegment_029_1701_0013, g32p_row02_traceSegment_029_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1674 27 27, g32p_row02_traceSegment_029_1674_0027, g32p_row02_traceSegment_029_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 1620 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1620 54 54, g32p_row02_traceSegment_029_1620_0054, g32p_row02_traceSegment_029_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 1512 216 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1512 108 108, g32p_row02_traceSegment_029_1512_0108, g32p_row02_traceSegment_029_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_029 1296 432 = [0, 0, 8, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1296 216 216, g32p_row02_traceSegment_029_1296_0216, g32p_row02_traceSegment_029_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_029 864 864 = [0, 0, 12, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 864 432 432, g32p_row02_traceSegment_029_0864_0432, g32p_row02_traceSegment_029_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_029 0 1728 = [0, 0, 25, 66] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 0 864 864, g32p_row02_traceSegment_029_0000_0864, g32p_row02_traceSegment_029_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1728 13 14, g32p_row02_traceSegment_029_1728_0013, g32p_row02_traceSegment_029_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1755 13 14, g32p_row02_traceSegment_029_1755_0013, g32p_row02_traceSegment_029_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1728 27 27, g32p_row02_traceSegment_029_1728_0027, g32p_row02_traceSegment_029_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1782 13 14, g32p_row02_traceSegment_029_1782_0013, g32p_row02_traceSegment_029_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1809 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1822 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1809 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1809 13 14, g32p_row02_traceSegment_029_1809_0013, g32p_row02_traceSegment_029_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1782 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1782 27 27, g32p_row02_traceSegment_029_1782_0027, g32p_row02_traceSegment_029_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 1728 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1728 54 54, g32p_row02_traceSegment_029_1728_0054, g32p_row02_traceSegment_029_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1836 13 14, g32p_row02_traceSegment_029_1836_0013, g32p_row02_traceSegment_029_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1863 13 14, g32p_row02_traceSegment_029_1863_0013, g32p_row02_traceSegment_029_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1836 27 27, g32p_row02_traceSegment_029_1836_0027, g32p_row02_traceSegment_029_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1890 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1903 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1890 27 = [0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1890 13 14, g32p_row02_traceSegment_029_1890_0013, g32p_row02_traceSegment_029_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1917 13 = [0, 0, 2, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1917 27 = [0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1917 13 14, g32p_row02_traceSegment_029_1917_0013, g32p_row02_traceSegment_029_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1890 54 = [0, 0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1890 27 27, g32p_row02_traceSegment_029_1890_0027, g32p_row02_traceSegment_029_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 1836 108 = [0, 0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1836 54 54, g32p_row02_traceSegment_029_1836_0054, g32p_row02_traceSegment_029_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 1728 216 = [0, 0, 5, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1728 108 108, g32p_row02_traceSegment_029_1728_0108, g32p_row02_traceSegment_029_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1944 13 14, g32p_row02_traceSegment_029_1944_0013, g32p_row02_traceSegment_029_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1971 13 14, g32p_row02_traceSegment_029_1971_0013, g32p_row02_traceSegment_029_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1944 27 27, g32p_row02_traceSegment_029_1944_0027, g32p_row02_traceSegment_029_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1998 13 14, g32p_row02_traceSegment_029_1998_0013, g32p_row02_traceSegment_029_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2038 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2025 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2025 13 14, g32p_row02_traceSegment_029_2025_0013, g32p_row02_traceSegment_029_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 1998 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1998 27 27, g32p_row02_traceSegment_029_1998_0027, g32p_row02_traceSegment_029_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 1944 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1944 54 54, g32p_row02_traceSegment_029_1944_0054, g32p_row02_traceSegment_029_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2052 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2065 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2052 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2052 13 14, g32p_row02_traceSegment_029_2052_0013, g32p_row02_traceSegment_029_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2079 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2079 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2079 13 14, g32p_row02_traceSegment_029_2079_0013, g32p_row02_traceSegment_029_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2052 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2052 27 27, g32p_row02_traceSegment_029_2052_0027, g32p_row02_traceSegment_029_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2106 13 14, g32p_row02_traceSegment_029_2106_0013, g32p_row02_traceSegment_029_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2133 13 14, g32p_row02_traceSegment_029_2133_0013, g32p_row02_traceSegment_029_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2106 27 27, g32p_row02_traceSegment_029_2106_0027, g32p_row02_traceSegment_029_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 2052 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2052 54 54, g32p_row02_traceSegment_029_2052_0054, g32p_row02_traceSegment_029_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 1944 216 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1944 108 108, g32p_row02_traceSegment_029_1944_0108, g32p_row02_traceSegment_029_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_029 1728 432 = [0, 0, 5, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1728 216 216, g32p_row02_traceSegment_029_1728_0216, g32p_row02_traceSegment_029_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2160 13 14, g32p_row02_traceSegment_029_2160_0013, g32p_row02_traceSegment_029_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2187 13 14, g32p_row02_traceSegment_029_2187_0013, g32p_row02_traceSegment_029_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2160 27 27, g32p_row02_traceSegment_029_2160_0027, g32p_row02_traceSegment_029_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2214 13 14, g32p_row02_traceSegment_029_2214_0013, g32p_row02_traceSegment_029_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2241 13 14, g32p_row02_traceSegment_029_2241_0013, g32p_row02_traceSegment_029_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2214 27 27, g32p_row02_traceSegment_029_2214_0027, g32p_row02_traceSegment_029_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2160 54 54, g32p_row02_traceSegment_029_2160_0054, g32p_row02_traceSegment_029_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2268 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2281 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2268 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2268 13 14, g32p_row02_traceSegment_029_2268_0013, g32p_row02_traceSegment_029_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2295 13 14, g32p_row02_traceSegment_029_2295_0013, g32p_row02_traceSegment_029_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2268 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2268 27 27, g32p_row02_traceSegment_029_2268_0027, g32p_row02_traceSegment_029_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2322 13 14, g32p_row02_traceSegment_029_2322_0013, g32p_row02_traceSegment_029_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2349 13 14, g32p_row02_traceSegment_029_2349_0013, g32p_row02_traceSegment_029_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2322 27 27, g32p_row02_traceSegment_029_2322_0027, g32p_row02_traceSegment_029_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 2268 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2268 54 54, g32p_row02_traceSegment_029_2268_0054, g32p_row02_traceSegment_029_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 2160 216 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2160 108 108, g32p_row02_traceSegment_029_2160_0108, g32p_row02_traceSegment_029_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2376 13 14, g32p_row02_traceSegment_029_2376_0013, g32p_row02_traceSegment_029_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2403 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2403 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2403 13 14, g32p_row02_traceSegment_029_2403_0013, g32p_row02_traceSegment_029_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2376 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2376 27 27, g32p_row02_traceSegment_029_2376_0027, g32p_row02_traceSegment_029_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2430 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2430 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2430 13 14, g32p_row02_traceSegment_029_2430_0013, g32p_row02_traceSegment_029_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2470 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2457 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2457 13 14, g32p_row02_traceSegment_029_2457_0013, g32p_row02_traceSegment_029_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2430 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2430 27 27, g32p_row02_traceSegment_029_2430_0027, g32p_row02_traceSegment_029_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 2376 108 = [0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2376 54 54, g32p_row02_traceSegment_029_2376_0054, g32p_row02_traceSegment_029_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2484 13 14, g32p_row02_traceSegment_029_2484_0013, g32p_row02_traceSegment_029_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2524 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2511 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2511 13 14, g32p_row02_traceSegment_029_2511_0013, g32p_row02_traceSegment_029_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2484 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2484 27 27, g32p_row02_traceSegment_029_2484_0027, g32p_row02_traceSegment_029_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2538 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2551 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2538 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2538 13 14, g32p_row02_traceSegment_029_2538_0013, g32p_row02_traceSegment_029_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2565 13 14, g32p_row02_traceSegment_029_2565_0013, g32p_row02_traceSegment_029_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2538 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2538 27 27, g32p_row02_traceSegment_029_2538_0027, g32p_row02_traceSegment_029_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 2484 108 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2484 54 54, g32p_row02_traceSegment_029_2484_0054, g32p_row02_traceSegment_029_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 2376 216 = [0, 0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2376 108 108, g32p_row02_traceSegment_029_2376_0108, g32p_row02_traceSegment_029_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_029 2160 432 = [0, 0, 1, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2160 216 216, g32p_row02_traceSegment_029_2160_0216, g32p_row02_traceSegment_029_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_029 1728 864 = [0, 0, 6, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1728 432 432, g32p_row02_traceSegment_029_1728_0432, g32p_row02_traceSegment_029_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2592 13 14, g32p_row02_traceSegment_029_2592_0013, g32p_row02_traceSegment_029_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2619 13 14, g32p_row02_traceSegment_029_2619_0013, g32p_row02_traceSegment_029_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2592 27 27, g32p_row02_traceSegment_029_2592_0027, g32p_row02_traceSegment_029_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2646 13 14, g32p_row02_traceSegment_029_2646_0013, g32p_row02_traceSegment_029_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2673 13 14, g32p_row02_traceSegment_029_2673_0013, g32p_row02_traceSegment_029_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2646 27 27, g32p_row02_traceSegment_029_2646_0027, g32p_row02_traceSegment_029_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2592 54 54, g32p_row02_traceSegment_029_2592_0054, g32p_row02_traceSegment_029_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2700 13 14, g32p_row02_traceSegment_029_2700_0013, g32p_row02_traceSegment_029_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2727 13 14, g32p_row02_traceSegment_029_2727_0013, g32p_row02_traceSegment_029_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2700 27 27, g32p_row02_traceSegment_029_2700_0027, g32p_row02_traceSegment_029_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2767 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2754 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2754 13 14, g32p_row02_traceSegment_029_2754_0013, g32p_row02_traceSegment_029_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2781 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2781 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2781 13 14, g32p_row02_traceSegment_029_2781_0013, g32p_row02_traceSegment_029_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2754 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2754 27 27, g32p_row02_traceSegment_029_2754_0027, g32p_row02_traceSegment_029_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 2700 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2700 54 54, g32p_row02_traceSegment_029_2700_0054, g32p_row02_traceSegment_029_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 2592 216 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2592 108 108, g32p_row02_traceSegment_029_2592_0108, g32p_row02_traceSegment_029_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2808 13 14, g32p_row02_traceSegment_029_2808_0013, g32p_row02_traceSegment_029_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2835 13 14, g32p_row02_traceSegment_029_2835_0013, g32p_row02_traceSegment_029_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2808 27 27, g32p_row02_traceSegment_029_2808_0027, g32p_row02_traceSegment_029_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2862 13 14, g32p_row02_traceSegment_029_2862_0013, g32p_row02_traceSegment_029_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2889 13 14, g32p_row02_traceSegment_029_2889_0013, g32p_row02_traceSegment_029_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2862 27 27, g32p_row02_traceSegment_029_2862_0027, g32p_row02_traceSegment_029_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2808 54 54, g32p_row02_traceSegment_029_2808_0054, g32p_row02_traceSegment_029_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2916 13 14, g32p_row02_traceSegment_029_2916_0013, g32p_row02_traceSegment_029_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2943 13 14, g32p_row02_traceSegment_029_2943_0013, g32p_row02_traceSegment_029_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2916 27 27, g32p_row02_traceSegment_029_2916_0027, g32p_row02_traceSegment_029_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2970 13 14, g32p_row02_traceSegment_029_2970_0013, g32p_row02_traceSegment_029_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2997 13 14, g32p_row02_traceSegment_029_2997_0013, g32p_row02_traceSegment_029_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2970 27 27, g32p_row02_traceSegment_029_2970_0027, g32p_row02_traceSegment_029_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2916 54 54, g32p_row02_traceSegment_029_2916_0054, g32p_row02_traceSegment_029_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2808 108 108, g32p_row02_traceSegment_029_2808_0108, g32p_row02_traceSegment_029_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_029 2592 432 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2592 216 216, g32p_row02_traceSegment_029_2592_0216, g32p_row02_traceSegment_029_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3037 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3024 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3024 13 14, g32p_row02_traceSegment_029_3024_0013, g32p_row02_traceSegment_029_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3051 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3064 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3051 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3051 13 14, g32p_row02_traceSegment_029_3051_0013, g32p_row02_traceSegment_029_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 3024 54 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3024 27 27, g32p_row02_traceSegment_029_3024_0027, g32p_row02_traceSegment_029_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3078 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3078 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3078 13 14, g32p_row02_traceSegment_029_3078_0013, g32p_row02_traceSegment_029_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3105 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3118 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3105 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3105 13 14, g32p_row02_traceSegment_029_3105_0013, g32p_row02_traceSegment_029_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 3078 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3078 27 27, g32p_row02_traceSegment_029_3078_0027, g32p_row02_traceSegment_029_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 3024 108 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3024 54 54, g32p_row02_traceSegment_029_3024_0054, g32p_row02_traceSegment_029_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3145 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3132 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3132 13 14, g32p_row02_traceSegment_029_3132_0013, g32p_row02_traceSegment_029_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3159 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3159 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3159 13 14, g32p_row02_traceSegment_029_3159_0013, g32p_row02_traceSegment_029_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 3132 54 = [0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3132 27 27, g32p_row02_traceSegment_029_3132_0027, g32p_row02_traceSegment_029_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3186 13 14, g32p_row02_traceSegment_029_3186_0013, g32p_row02_traceSegment_029_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3213 13 14, g32p_row02_traceSegment_029_3213_0013, g32p_row02_traceSegment_029_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3186 27 27, g32p_row02_traceSegment_029_3186_0027, g32p_row02_traceSegment_029_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 3132 108 = [0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3132 54 54, g32p_row02_traceSegment_029_3132_0054, g32p_row02_traceSegment_029_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 3024 216 = [0, 0, 1, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3024 108 108, g32p_row02_traceSegment_029_3024_0108, g32p_row02_traceSegment_029_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3240 13 14, g32p_row02_traceSegment_029_3240_0013, g32p_row02_traceSegment_029_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3267 13 14, g32p_row02_traceSegment_029_3267_0013, g32p_row02_traceSegment_029_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3240 27 27, g32p_row02_traceSegment_029_3240_0027, g32p_row02_traceSegment_029_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3294 13 14, g32p_row02_traceSegment_029_3294_0013, g32p_row02_traceSegment_029_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3321 13 14, g32p_row02_traceSegment_029_3321_0013, g32p_row02_traceSegment_029_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3294 27 27, g32p_row02_traceSegment_029_3294_0027, g32p_row02_traceSegment_029_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3240 54 54, g32p_row02_traceSegment_029_3240_0054, g32p_row02_traceSegment_029_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3348 13 14, g32p_row02_traceSegment_029_3348_0013, g32p_row02_traceSegment_029_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3375 13 14, g32p_row02_traceSegment_029_3375_0013, g32p_row02_traceSegment_029_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3348 27 27, g32p_row02_traceSegment_029_3348_0027, g32p_row02_traceSegment_029_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3402 13 14, g32p_row02_traceSegment_029_3402_0013, g32p_row02_traceSegment_029_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_029 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_029 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_029_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_029 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3429 13 14, g32p_row02_traceSegment_029_3429_0013, g32p_row02_traceSegment_029_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_029 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3402 27 27, g32p_row02_traceSegment_029_3402_0027, g32p_row02_traceSegment_029_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_029 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3348 54 54, g32p_row02_traceSegment_029_3348_0054, g32p_row02_traceSegment_029_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_029 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3240 108 108, g32p_row02_traceSegment_029_3240_0108, g32p_row02_traceSegment_029_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_029_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_029 3024 432 = [0, 0, 1, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 3024 216 216, g32p_row02_traceSegment_029_3024_0216, g32p_row02_traceSegment_029_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_029_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_029 2592 864 = [0, 0, 1, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 2592 432 432, g32p_row02_traceSegment_029_2592_0432, g32p_row02_traceSegment_029_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_029_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_029 1728 1728 = [0, 0, 7, 30] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 1728 864 864, g32p_row02_traceSegment_029_1728_0864, g32p_row02_traceSegment_029_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_029_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_029 0 3456 = [0, 0, 32, 96] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_029 0 1728 1728, g32p_row02_traceSegment_029_0000_1728, g32p_row02_traceSegment_029_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 29 = [0, 0, 32, 96] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_029_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 20) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 20) (g32p_literalTraceValue 1 20)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_020]
  decide +kernel

theorem g32p_row02_tracePolynomial_021 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 21) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 21) (g32p_literalTraceValue 1 21)
      [1, -1, 1] [-3456, 0, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_021]
  decide +kernel

theorem g32p_row02_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 23) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 23) (g32p_literalTraceValue 1 23)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_023]
  decide +kernel

theorem g32p_row02_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 24) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 24) (g32p_literalTraceValue 1 24)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row02_traceCoefficients_024]
  decide +kernel

theorem g32p_row02_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 25) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 25) (g32p_literalTraceValue 1 25)
      [1, -1, 1] [13824, 13824, 3456] = true := by
  rw [g32p_row02_traceCoefficients_025]
  decide +kernel

theorem g32p_row02_tracePolynomial_027 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 27) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 27) (g32p_literalTraceValue 1 27)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_027]
  decide +kernel

theorem g32p_row02_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 28) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 28) (g32p_literalTraceValue 1 28)
      [1, -1, 1] [31104, 31104, 31104] = true := by
  rw [g32p_row02_traceCoefficients_028]
  decide +kernel

theorem g32p_row02_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 29) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 29) (g32p_literalTraceValue 1 29)
      [1, -1, 1] [10368, 10368] = true := by
  rw [g32p_row02_traceCoefficients_029]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
