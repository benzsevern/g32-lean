import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_063 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 63 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_063_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 0 13 14, g32p_row02_traceSegment_063_0000_0013, g32p_row02_traceSegment_063_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 27 13 14, g32p_row02_traceSegment_063_0027_0013, g32p_row02_traceSegment_063_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 0 27 27, g32p_row02_traceSegment_063_0000_0027, g32p_row02_traceSegment_063_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 54 13 14, g32p_row02_traceSegment_063_0054_0013, g32p_row02_traceSegment_063_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 94 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 81 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 81 13 14, g32p_row02_traceSegment_063_0081_0013, g32p_row02_traceSegment_063_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 54 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 54 27 27, g32p_row02_traceSegment_063_0054_0027, g32p_row02_traceSegment_063_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 0 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 0 54 54, g32p_row02_traceSegment_063_0000_0054, g32p_row02_traceSegment_063_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 108 13 14, g32p_row02_traceSegment_063_0108_0013, g32p_row02_traceSegment_063_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 148 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 135 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 135 13 14, g32p_row02_traceSegment_063_0135_0013, g32p_row02_traceSegment_063_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 108 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 108 27 27, g32p_row02_traceSegment_063_0108_0027, g32p_row02_traceSegment_063_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 162 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 175 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 162 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 162 13 14, g32p_row02_traceSegment_063_0162_0013, g32p_row02_traceSegment_063_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 189 13 14, g32p_row02_traceSegment_063_0189_0013, g32p_row02_traceSegment_063_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 162 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 162 27 27, g32p_row02_traceSegment_063_0162_0027, g32p_row02_traceSegment_063_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 108 108 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 108 54 54, g32p_row02_traceSegment_063_0108_0054, g32p_row02_traceSegment_063_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 0 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 0 108 108, g32p_row02_traceSegment_063_0000_0108, g32p_row02_traceSegment_063_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 216 13 14, g32p_row02_traceSegment_063_0216_0013, g32p_row02_traceSegment_063_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 256 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 243 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 243 13 14, g32p_row02_traceSegment_063_0243_0013, g32p_row02_traceSegment_063_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 216 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 216 27 27, g32p_row02_traceSegment_063_0216_0027, g32p_row02_traceSegment_063_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 270 13 14, g32p_row02_traceSegment_063_0270_0013, g32p_row02_traceSegment_063_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 297 13 14, g32p_row02_traceSegment_063_0297_0013, g32p_row02_traceSegment_063_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 270 27 27, g32p_row02_traceSegment_063_0270_0027, g32p_row02_traceSegment_063_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 216 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 216 54 54, g32p_row02_traceSegment_063_0216_0054, g32p_row02_traceSegment_063_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 324 13 14, g32p_row02_traceSegment_063_0324_0013, g32p_row02_traceSegment_063_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 351 13 14, g32p_row02_traceSegment_063_0351_0013, g32p_row02_traceSegment_063_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 324 27 27, g32p_row02_traceSegment_063_0324_0027, g32p_row02_traceSegment_063_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 391 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 378 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 378 13 14, g32p_row02_traceSegment_063_0378_0013, g32p_row02_traceSegment_063_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 405 13 14, g32p_row02_traceSegment_063_0405_0013, g32p_row02_traceSegment_063_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 378 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 378 27 27, g32p_row02_traceSegment_063_0378_0027, g32p_row02_traceSegment_063_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 324 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 324 54 54, g32p_row02_traceSegment_063_0324_0054, g32p_row02_traceSegment_063_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 216 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 216 108 108, g32p_row02_traceSegment_063_0216_0108, g32p_row02_traceSegment_063_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_063 0 432 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 0 216 216, g32p_row02_traceSegment_063_0000_0216, g32p_row02_traceSegment_063_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 432 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 445 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 432 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 432 13 14, g32p_row02_traceSegment_063_0432_0013, g32p_row02_traceSegment_063_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 459 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 459 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 459 13 14, g32p_row02_traceSegment_063_0459_0013, g32p_row02_traceSegment_063_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 432 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 432 27 27, g32p_row02_traceSegment_063_0432_0027, g32p_row02_traceSegment_063_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 486 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 486 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 486 13 14, g32p_row02_traceSegment_063_0486_0013, g32p_row02_traceSegment_063_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 513 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 513 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 513 13 14, g32p_row02_traceSegment_063_0513_0013, g32p_row02_traceSegment_063_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 486 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 486 27 27, g32p_row02_traceSegment_063_0486_0027, g32p_row02_traceSegment_063_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 432 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 432 54 54, g32p_row02_traceSegment_063_0432_0054, g32p_row02_traceSegment_063_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 540 13 14, g32p_row02_traceSegment_063_0540_0013, g32p_row02_traceSegment_063_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 567 13 14, g32p_row02_traceSegment_063_0567_0013, g32p_row02_traceSegment_063_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 540 27 27, g32p_row02_traceSegment_063_0540_0027, g32p_row02_traceSegment_063_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 594 13 14, g32p_row02_traceSegment_063_0594_0013, g32p_row02_traceSegment_063_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 621 13 14, g32p_row02_traceSegment_063_0621_0013, g32p_row02_traceSegment_063_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 594 27 27, g32p_row02_traceSegment_063_0594_0027, g32p_row02_traceSegment_063_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 540 54 54, g32p_row02_traceSegment_063_0540_0054, g32p_row02_traceSegment_063_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 432 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 432 108 108, g32p_row02_traceSegment_063_0432_0108, g32p_row02_traceSegment_063_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 648 13 14, g32p_row02_traceSegment_063_0648_0013, g32p_row02_traceSegment_063_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 675 13 14, g32p_row02_traceSegment_063_0675_0013, g32p_row02_traceSegment_063_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 648 27 27, g32p_row02_traceSegment_063_0648_0027, g32p_row02_traceSegment_063_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 702 13 14, g32p_row02_traceSegment_063_0702_0013, g32p_row02_traceSegment_063_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 729 13 14, g32p_row02_traceSegment_063_0729_0013, g32p_row02_traceSegment_063_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 702 27 27, g32p_row02_traceSegment_063_0702_0027, g32p_row02_traceSegment_063_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 648 54 54, g32p_row02_traceSegment_063_0648_0054, g32p_row02_traceSegment_063_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 756 13 14, g32p_row02_traceSegment_063_0756_0013, g32p_row02_traceSegment_063_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 783 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 783 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 783 13 14, g32p_row02_traceSegment_063_0783_0013, g32p_row02_traceSegment_063_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 756 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 756 27 27, g32p_row02_traceSegment_063_0756_0027, g32p_row02_traceSegment_063_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 810 13 14, g32p_row02_traceSegment_063_0810_0013, g32p_row02_traceSegment_063_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 850 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 837 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 837 13 14, g32p_row02_traceSegment_063_0837_0013, g32p_row02_traceSegment_063_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 810 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 810 27 27, g32p_row02_traceSegment_063_0810_0027, g32p_row02_traceSegment_063_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 756 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 756 54 54, g32p_row02_traceSegment_063_0756_0054, g32p_row02_traceSegment_063_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 648 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 648 108 108, g32p_row02_traceSegment_063_0648_0108, g32p_row02_traceSegment_063_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_063 432 432 = [9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 432 216 216, g32p_row02_traceSegment_063_0432_0216, g32p_row02_traceSegment_063_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_063 0 864 = [17] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 0 432 432, g32p_row02_traceSegment_063_0000_0432, g32p_row02_traceSegment_063_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 864 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 864 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 864 13 14, g32p_row02_traceSegment_063_0864_0013, g32p_row02_traceSegment_063_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 891 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 891 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 891 13 14, g32p_row02_traceSegment_063_0891_0013, g32p_row02_traceSegment_063_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 864 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 864 27 27, g32p_row02_traceSegment_063_0864_0027, g32p_row02_traceSegment_063_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 918 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 918 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 918 13 14, g32p_row02_traceSegment_063_0918_0013, g32p_row02_traceSegment_063_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 945 13 14, g32p_row02_traceSegment_063_0945_0013, g32p_row02_traceSegment_063_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 918 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 918 27 27, g32p_row02_traceSegment_063_0918_0027, g32p_row02_traceSegment_063_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 864 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 864 54 54, g32p_row02_traceSegment_063_0864_0054, g32p_row02_traceSegment_063_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 972 13 14, g32p_row02_traceSegment_063_0972_0013, g32p_row02_traceSegment_063_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 999 13 14, g32p_row02_traceSegment_063_0999_0013, g32p_row02_traceSegment_063_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 972 27 27, g32p_row02_traceSegment_063_0972_0027, g32p_row02_traceSegment_063_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1026 13 14, g32p_row02_traceSegment_063_1026_0013, g32p_row02_traceSegment_063_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1053 13 14, g32p_row02_traceSegment_063_1053_0013, g32p_row02_traceSegment_063_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1026 27 27, g32p_row02_traceSegment_063_1026_0027, g32p_row02_traceSegment_063_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 972 54 54, g32p_row02_traceSegment_063_0972_0054, g32p_row02_traceSegment_063_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 864 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 864 108 108, g32p_row02_traceSegment_063_0864_0108, g32p_row02_traceSegment_063_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1093 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1080 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1080 13 14, g32p_row02_traceSegment_063_1080_0013, g32p_row02_traceSegment_063_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1107 13 14, g32p_row02_traceSegment_063_1107_0013, g32p_row02_traceSegment_063_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1080 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1080 27 27, g32p_row02_traceSegment_063_1080_0027, g32p_row02_traceSegment_063_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1134 13 14, g32p_row02_traceSegment_063_1134_0013, g32p_row02_traceSegment_063_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1161 13 14, g32p_row02_traceSegment_063_1161_0013, g32p_row02_traceSegment_063_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1134 27 27, g32p_row02_traceSegment_063_1134_0027, g32p_row02_traceSegment_063_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 1080 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1080 54 54, g32p_row02_traceSegment_063_1080_0054, g32p_row02_traceSegment_063_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1188 13 14, g32p_row02_traceSegment_063_1188_0013, g32p_row02_traceSegment_063_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1215 13 14, g32p_row02_traceSegment_063_1215_0013, g32p_row02_traceSegment_063_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1188 27 27, g32p_row02_traceSegment_063_1188_0027, g32p_row02_traceSegment_063_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1242 13 14, g32p_row02_traceSegment_063_1242_0013, g32p_row02_traceSegment_063_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1269 13 14, g32p_row02_traceSegment_063_1269_0013, g32p_row02_traceSegment_063_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1242 27 27, g32p_row02_traceSegment_063_1242_0027, g32p_row02_traceSegment_063_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1188 54 54, g32p_row02_traceSegment_063_1188_0054, g32p_row02_traceSegment_063_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 1080 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1080 108 108, g32p_row02_traceSegment_063_1080_0108, g32p_row02_traceSegment_063_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_063 864 432 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 864 216 216, g32p_row02_traceSegment_063_0864_0216, g32p_row02_traceSegment_063_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1296 13 14, g32p_row02_traceSegment_063_1296_0013, g32p_row02_traceSegment_063_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1323 13 14, g32p_row02_traceSegment_063_1323_0013, g32p_row02_traceSegment_063_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1296 27 27, g32p_row02_traceSegment_063_1296_0027, g32p_row02_traceSegment_063_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1350 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1350 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1350 13 14, g32p_row02_traceSegment_063_1350_0013, g32p_row02_traceSegment_063_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1377 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1377 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1377 13 14, g32p_row02_traceSegment_063_1377_0013, g32p_row02_traceSegment_063_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1350 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1350 27 27, g32p_row02_traceSegment_063_1350_0027, g32p_row02_traceSegment_063_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 1296 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1296 54 54, g32p_row02_traceSegment_063_1296_0054, g32p_row02_traceSegment_063_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1404 13 14, g32p_row02_traceSegment_063_1404_0013, g32p_row02_traceSegment_063_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1431 13 14, g32p_row02_traceSegment_063_1431_0013, g32p_row02_traceSegment_063_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1404 27 27, g32p_row02_traceSegment_063_1404_0027, g32p_row02_traceSegment_063_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1458 13 14, g32p_row02_traceSegment_063_1458_0013, g32p_row02_traceSegment_063_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1485 13 14, g32p_row02_traceSegment_063_1485_0013, g32p_row02_traceSegment_063_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1458 27 27, g32p_row02_traceSegment_063_1458_0027, g32p_row02_traceSegment_063_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1404 54 54, g32p_row02_traceSegment_063_1404_0054, g32p_row02_traceSegment_063_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 1296 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1296 108 108, g32p_row02_traceSegment_063_1296_0108, g32p_row02_traceSegment_063_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1512 13 14, g32p_row02_traceSegment_063_1512_0013, g32p_row02_traceSegment_063_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1539 13 14, g32p_row02_traceSegment_063_1539_0013, g32p_row02_traceSegment_063_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1512 27 27, g32p_row02_traceSegment_063_1512_0027, g32p_row02_traceSegment_063_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1566 13 14, g32p_row02_traceSegment_063_1566_0013, g32p_row02_traceSegment_063_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1593 13 14, g32p_row02_traceSegment_063_1593_0013, g32p_row02_traceSegment_063_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1566 27 27, g32p_row02_traceSegment_063_1566_0027, g32p_row02_traceSegment_063_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1512 54 54, g32p_row02_traceSegment_063_1512_0054, g32p_row02_traceSegment_063_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1620 13 14, g32p_row02_traceSegment_063_1620_0013, g32p_row02_traceSegment_063_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1647 13 14, g32p_row02_traceSegment_063_1647_0013, g32p_row02_traceSegment_063_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1620 27 27, g32p_row02_traceSegment_063_1620_0027, g32p_row02_traceSegment_063_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1687 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1674 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1674 13 14, g32p_row02_traceSegment_063_1674_0013, g32p_row02_traceSegment_063_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1701 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1701 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1701 13 14, g32p_row02_traceSegment_063_1701_0013, g32p_row02_traceSegment_063_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1674 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1674 27 27, g32p_row02_traceSegment_063_1674_0027, g32p_row02_traceSegment_063_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 1620 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1620 54 54, g32p_row02_traceSegment_063_1620_0054, g32p_row02_traceSegment_063_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 1512 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1512 108 108, g32p_row02_traceSegment_063_1512_0108, g32p_row02_traceSegment_063_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_063 1296 432 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1296 216 216, g32p_row02_traceSegment_063_1296_0216, g32p_row02_traceSegment_063_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_063 864 864 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 864 432 432, g32p_row02_traceSegment_063_0864_0432, g32p_row02_traceSegment_063_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_063 0 1728 = [27] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 0 864 864, g32p_row02_traceSegment_063_0000_0864, g32p_row02_traceSegment_063_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1728 13 14, g32p_row02_traceSegment_063_1728_0013, g32p_row02_traceSegment_063_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1755 13 14, g32p_row02_traceSegment_063_1755_0013, g32p_row02_traceSegment_063_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1728 27 27, g32p_row02_traceSegment_063_1728_0027, g32p_row02_traceSegment_063_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1795 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1782 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1782 13 14, g32p_row02_traceSegment_063_1782_0013, g32p_row02_traceSegment_063_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1822 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1809 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1809 13 14, g32p_row02_traceSegment_063_1809_0013, g32p_row02_traceSegment_063_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1782 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1782 27 27, g32p_row02_traceSegment_063_1782_0027, g32p_row02_traceSegment_063_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 1728 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1728 54 54, g32p_row02_traceSegment_063_1728_0054, g32p_row02_traceSegment_063_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1836 13 14, g32p_row02_traceSegment_063_1836_0013, g32p_row02_traceSegment_063_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1863 13 14, g32p_row02_traceSegment_063_1863_0013, g32p_row02_traceSegment_063_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1836 27 27, g32p_row02_traceSegment_063_1836_0027, g32p_row02_traceSegment_063_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1890 13 14, g32p_row02_traceSegment_063_1890_0013, g32p_row02_traceSegment_063_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1917 13 14, g32p_row02_traceSegment_063_1917_0013, g32p_row02_traceSegment_063_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1890 27 27, g32p_row02_traceSegment_063_1890_0027, g32p_row02_traceSegment_063_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1836 54 54, g32p_row02_traceSegment_063_1836_0054, g32p_row02_traceSegment_063_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 1728 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1728 108 108, g32p_row02_traceSegment_063_1728_0108, g32p_row02_traceSegment_063_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1944 13 14, g32p_row02_traceSegment_063_1944_0013, g32p_row02_traceSegment_063_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1971 13 14, g32p_row02_traceSegment_063_1971_0013, g32p_row02_traceSegment_063_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1944 27 27, g32p_row02_traceSegment_063_1944_0027, g32p_row02_traceSegment_063_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 1998 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 1998 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1998 13 14, g32p_row02_traceSegment_063_1998_0013, g32p_row02_traceSegment_063_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2038 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2025 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2025 13 14, g32p_row02_traceSegment_063_2025_0013, g32p_row02_traceSegment_063_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 1998 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1998 27 27, g32p_row02_traceSegment_063_1998_0027, g32p_row02_traceSegment_063_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 1944 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1944 54 54, g32p_row02_traceSegment_063_1944_0054, g32p_row02_traceSegment_063_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2052 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2052 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2052 13 14, g32p_row02_traceSegment_063_2052_0013, g32p_row02_traceSegment_063_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2079 13 14, g32p_row02_traceSegment_063_2079_0013, g32p_row02_traceSegment_063_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2052 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2052 27 27, g32p_row02_traceSegment_063_2052_0027, g32p_row02_traceSegment_063_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2119 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2106 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2106 13 14, g32p_row02_traceSegment_063_2106_0013, g32p_row02_traceSegment_063_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2133 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2133 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2133 13 14, g32p_row02_traceSegment_063_2133_0013, g32p_row02_traceSegment_063_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2106 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2106 27 27, g32p_row02_traceSegment_063_2106_0027, g32p_row02_traceSegment_063_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 2052 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2052 54 54, g32p_row02_traceSegment_063_2052_0054, g32p_row02_traceSegment_063_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 1944 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1944 108 108, g32p_row02_traceSegment_063_1944_0108, g32p_row02_traceSegment_063_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_063 1728 432 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1728 216 216, g32p_row02_traceSegment_063_1728_0216, g32p_row02_traceSegment_063_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2160 13 14, g32p_row02_traceSegment_063_2160_0013, g32p_row02_traceSegment_063_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2187 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2187 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2187 13 14, g32p_row02_traceSegment_063_2187_0013, g32p_row02_traceSegment_063_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2160 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2160 27 27, g32p_row02_traceSegment_063_2160_0027, g32p_row02_traceSegment_063_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2227 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2214 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2214 13 14, g32p_row02_traceSegment_063_2214_0013, g32p_row02_traceSegment_063_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2254 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2241 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2241 13 14, g32p_row02_traceSegment_063_2241_0013, g32p_row02_traceSegment_063_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2214 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2214 27 27, g32p_row02_traceSegment_063_2214_0027, g32p_row02_traceSegment_063_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 2160 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2160 54 54, g32p_row02_traceSegment_063_2160_0054, g32p_row02_traceSegment_063_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2268 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2268 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2268 13 14, g32p_row02_traceSegment_063_2268_0013, g32p_row02_traceSegment_063_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2295 13 14, g32p_row02_traceSegment_063_2295_0013, g32p_row02_traceSegment_063_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2268 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2268 27 27, g32p_row02_traceSegment_063_2268_0027, g32p_row02_traceSegment_063_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2322 13 14, g32p_row02_traceSegment_063_2322_0013, g32p_row02_traceSegment_063_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2362 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2349 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2349 13 14, g32p_row02_traceSegment_063_2349_0013, g32p_row02_traceSegment_063_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2322 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2322 27 27, g32p_row02_traceSegment_063_2322_0027, g32p_row02_traceSegment_063_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 2268 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2268 54 54, g32p_row02_traceSegment_063_2268_0054, g32p_row02_traceSegment_063_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 2160 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2160 108 108, g32p_row02_traceSegment_063_2160_0108, g32p_row02_traceSegment_063_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2376 13 14, g32p_row02_traceSegment_063_2376_0013, g32p_row02_traceSegment_063_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2403 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2403 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2403 13 14, g32p_row02_traceSegment_063_2403_0013, g32p_row02_traceSegment_063_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2376 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2376 27 27, g32p_row02_traceSegment_063_2376_0027, g32p_row02_traceSegment_063_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2430 13 14, g32p_row02_traceSegment_063_2430_0013, g32p_row02_traceSegment_063_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2457 13 14, g32p_row02_traceSegment_063_2457_0013, g32p_row02_traceSegment_063_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2430 27 27, g32p_row02_traceSegment_063_2430_0027, g32p_row02_traceSegment_063_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 2376 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2376 54 54, g32p_row02_traceSegment_063_2376_0054, g32p_row02_traceSegment_063_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2497 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2484 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2484 13 14, g32p_row02_traceSegment_063_2484_0013, g32p_row02_traceSegment_063_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2524 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2511 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2511 13 14, g32p_row02_traceSegment_063_2511_0013, g32p_row02_traceSegment_063_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2484 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2484 27 27, g32p_row02_traceSegment_063_2484_0027, g32p_row02_traceSegment_063_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2538 13 14, g32p_row02_traceSegment_063_2538_0013, g32p_row02_traceSegment_063_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2565 13 14, g32p_row02_traceSegment_063_2565_0013, g32p_row02_traceSegment_063_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2538 27 27, g32p_row02_traceSegment_063_2538_0027, g32p_row02_traceSegment_063_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 2484 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2484 54 54, g32p_row02_traceSegment_063_2484_0054, g32p_row02_traceSegment_063_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 2376 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2376 108 108, g32p_row02_traceSegment_063_2376_0108, g32p_row02_traceSegment_063_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_063 2160 432 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2160 216 216, g32p_row02_traceSegment_063_2160_0216, g32p_row02_traceSegment_063_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_063 1728 864 = [18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1728 432 432, g32p_row02_traceSegment_063_1728_0432, g32p_row02_traceSegment_063_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2592 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2605 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2592 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2592 13 14, g32p_row02_traceSegment_063_2592_0013, g32p_row02_traceSegment_063_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2619 13 14, g32p_row02_traceSegment_063_2619_0013, g32p_row02_traceSegment_063_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2592 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2592 27 27, g32p_row02_traceSegment_063_2592_0027, g32p_row02_traceSegment_063_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2646 13 14, g32p_row02_traceSegment_063_2646_0013, g32p_row02_traceSegment_063_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2673 13 14, g32p_row02_traceSegment_063_2673_0013, g32p_row02_traceSegment_063_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2646 27 27, g32p_row02_traceSegment_063_2646_0027, g32p_row02_traceSegment_063_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 2592 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2592 54 54, g32p_row02_traceSegment_063_2592_0054, g32p_row02_traceSegment_063_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2700 13 14, g32p_row02_traceSegment_063_2700_0013, g32p_row02_traceSegment_063_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2727 13 14, g32p_row02_traceSegment_063_2727_0013, g32p_row02_traceSegment_063_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2700 27 27, g32p_row02_traceSegment_063_2700_0027, g32p_row02_traceSegment_063_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2754 13 14, g32p_row02_traceSegment_063_2754_0013, g32p_row02_traceSegment_063_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2781 13 14, g32p_row02_traceSegment_063_2781_0013, g32p_row02_traceSegment_063_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2754 27 27, g32p_row02_traceSegment_063_2754_0027, g32p_row02_traceSegment_063_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2700 54 54, g32p_row02_traceSegment_063_2700_0054, g32p_row02_traceSegment_063_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 2592 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2592 108 108, g32p_row02_traceSegment_063_2592_0108, g32p_row02_traceSegment_063_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2808 13 14, g32p_row02_traceSegment_063_2808_0013, g32p_row02_traceSegment_063_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2835 13 14, g32p_row02_traceSegment_063_2835_0013, g32p_row02_traceSegment_063_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2808 27 27, g32p_row02_traceSegment_063_2808_0027, g32p_row02_traceSegment_063_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2862 13 14, g32p_row02_traceSegment_063_2862_0013, g32p_row02_traceSegment_063_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2889 13 14, g32p_row02_traceSegment_063_2889_0013, g32p_row02_traceSegment_063_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2862 27 27, g32p_row02_traceSegment_063_2862_0027, g32p_row02_traceSegment_063_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2808 54 54, g32p_row02_traceSegment_063_2808_0054, g32p_row02_traceSegment_063_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2916 13 14, g32p_row02_traceSegment_063_2916_0013, g32p_row02_traceSegment_063_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2943 13 14, g32p_row02_traceSegment_063_2943_0013, g32p_row02_traceSegment_063_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2916 27 27, g32p_row02_traceSegment_063_2916_0027, g32p_row02_traceSegment_063_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2970 13 14, g32p_row02_traceSegment_063_2970_0013, g32p_row02_traceSegment_063_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2997 13 14, g32p_row02_traceSegment_063_2997_0013, g32p_row02_traceSegment_063_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2970 27 27, g32p_row02_traceSegment_063_2970_0027, g32p_row02_traceSegment_063_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2916 54 54, g32p_row02_traceSegment_063_2916_0054, g32p_row02_traceSegment_063_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2808 108 108, g32p_row02_traceSegment_063_2808_0108, g32p_row02_traceSegment_063_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_063 2592 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2592 216 216, g32p_row02_traceSegment_063_2592_0216, g32p_row02_traceSegment_063_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3024 13 14, g32p_row02_traceSegment_063_3024_0013, g32p_row02_traceSegment_063_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3051 13 14, g32p_row02_traceSegment_063_3051_0013, g32p_row02_traceSegment_063_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3024 27 27, g32p_row02_traceSegment_063_3024_0027, g32p_row02_traceSegment_063_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3078 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3078 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3078 13 14, g32p_row02_traceSegment_063_3078_0013, g32p_row02_traceSegment_063_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3105 13 14, g32p_row02_traceSegment_063_3105_0013, g32p_row02_traceSegment_063_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 3078 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3078 27 27, g32p_row02_traceSegment_063_3078_0027, g32p_row02_traceSegment_063_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 3024 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3024 54 54, g32p_row02_traceSegment_063_3024_0054, g32p_row02_traceSegment_063_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3132 13 14, g32p_row02_traceSegment_063_3132_0013, g32p_row02_traceSegment_063_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3159 13 14, g32p_row02_traceSegment_063_3159_0013, g32p_row02_traceSegment_063_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3132 27 27, g32p_row02_traceSegment_063_3132_0027, g32p_row02_traceSegment_063_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3186 13 14, g32p_row02_traceSegment_063_3186_0013, g32p_row02_traceSegment_063_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3213 13 14, g32p_row02_traceSegment_063_3213_0013, g32p_row02_traceSegment_063_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3186 27 27, g32p_row02_traceSegment_063_3186_0027, g32p_row02_traceSegment_063_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3132 54 54, g32p_row02_traceSegment_063_3132_0054, g32p_row02_traceSegment_063_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 3024 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3024 108 108, g32p_row02_traceSegment_063_3024_0108, g32p_row02_traceSegment_063_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3240 13 14, g32p_row02_traceSegment_063_3240_0013, g32p_row02_traceSegment_063_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3267 13 14, g32p_row02_traceSegment_063_3267_0013, g32p_row02_traceSegment_063_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3240 27 27, g32p_row02_traceSegment_063_3240_0027, g32p_row02_traceSegment_063_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3294 13 14, g32p_row02_traceSegment_063_3294_0013, g32p_row02_traceSegment_063_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3321 13 14, g32p_row02_traceSegment_063_3321_0013, g32p_row02_traceSegment_063_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3294 27 27, g32p_row02_traceSegment_063_3294_0027, g32p_row02_traceSegment_063_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3240 54 54, g32p_row02_traceSegment_063_3240_0054, g32p_row02_traceSegment_063_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3348 13 14, g32p_row02_traceSegment_063_3348_0013, g32p_row02_traceSegment_063_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3375 13 14, g32p_row02_traceSegment_063_3375_0013, g32p_row02_traceSegment_063_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3348 27 27, g32p_row02_traceSegment_063_3348_0027, g32p_row02_traceSegment_063_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3402 13 14, g32p_row02_traceSegment_063_3402_0013, g32p_row02_traceSegment_063_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_063 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_063 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_063_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_063 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3429 13 14, g32p_row02_traceSegment_063_3429_0013, g32p_row02_traceSegment_063_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_063 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3402 27 27, g32p_row02_traceSegment_063_3402_0027, g32p_row02_traceSegment_063_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_063 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3348 54 54, g32p_row02_traceSegment_063_3348_0054, g32p_row02_traceSegment_063_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_063 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3240 108 108, g32p_row02_traceSegment_063_3240_0108, g32p_row02_traceSegment_063_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_063_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_063 3024 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 3024 216 216, g32p_row02_traceSegment_063_3024_0216, g32p_row02_traceSegment_063_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_063_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_063 2592 864 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 2592 432 432, g32p_row02_traceSegment_063_2592_0432, g32p_row02_traceSegment_063_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_063_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_063 1728 1728 = [21] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 1728 864 864, g32p_row02_traceSegment_063_1728_0864, g32p_row02_traceSegment_063_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_063_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_063 0 3456 = [48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_063 0 1728 1728, g32p_row02_traceSegment_063_0000_1728, g32p_row02_traceSegment_063_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_063 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 63 = [48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_063_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_064 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 64 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_064_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 0 13 14, g32p_row02_traceSegment_064_0000_0013, g32p_row02_traceSegment_064_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 27 13 14, g32p_row02_traceSegment_064_0027_0013, g32p_row02_traceSegment_064_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 0 27 27, g32p_row02_traceSegment_064_0000_0027, g32p_row02_traceSegment_064_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 54 13 14, g32p_row02_traceSegment_064_0054_0013, g32p_row02_traceSegment_064_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 81 13 14, g32p_row02_traceSegment_064_0081_0013, g32p_row02_traceSegment_064_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 54 27 27, g32p_row02_traceSegment_064_0054_0027, g32p_row02_traceSegment_064_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 0 54 54, g32p_row02_traceSegment_064_0000_0054, g32p_row02_traceSegment_064_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 108 13 14, g32p_row02_traceSegment_064_0108_0013, g32p_row02_traceSegment_064_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 135 13 14, g32p_row02_traceSegment_064_0135_0013, g32p_row02_traceSegment_064_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 108 27 27, g32p_row02_traceSegment_064_0108_0027, g32p_row02_traceSegment_064_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 162 13 14, g32p_row02_traceSegment_064_0162_0013, g32p_row02_traceSegment_064_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 189 13 14, g32p_row02_traceSegment_064_0189_0013, g32p_row02_traceSegment_064_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 162 27 27, g32p_row02_traceSegment_064_0162_0027, g32p_row02_traceSegment_064_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 108 54 54, g32p_row02_traceSegment_064_0108_0054, g32p_row02_traceSegment_064_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 0 108 108, g32p_row02_traceSegment_064_0000_0108, g32p_row02_traceSegment_064_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 216 13 14, g32p_row02_traceSegment_064_0216_0013, g32p_row02_traceSegment_064_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 243 13 14, g32p_row02_traceSegment_064_0243_0013, g32p_row02_traceSegment_064_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 216 27 27, g32p_row02_traceSegment_064_0216_0027, g32p_row02_traceSegment_064_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 270 13 14, g32p_row02_traceSegment_064_0270_0013, g32p_row02_traceSegment_064_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 297 13 14, g32p_row02_traceSegment_064_0297_0013, g32p_row02_traceSegment_064_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 270 27 27, g32p_row02_traceSegment_064_0270_0027, g32p_row02_traceSegment_064_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 216 54 54, g32p_row02_traceSegment_064_0216_0054, g32p_row02_traceSegment_064_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 324 13 14, g32p_row02_traceSegment_064_0324_0013, g32p_row02_traceSegment_064_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 351 13 14, g32p_row02_traceSegment_064_0351_0013, g32p_row02_traceSegment_064_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 324 27 27, g32p_row02_traceSegment_064_0324_0027, g32p_row02_traceSegment_064_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 378 13 14, g32p_row02_traceSegment_064_0378_0013, g32p_row02_traceSegment_064_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 405 13 14, g32p_row02_traceSegment_064_0405_0013, g32p_row02_traceSegment_064_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 378 27 27, g32p_row02_traceSegment_064_0378_0027, g32p_row02_traceSegment_064_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 324 54 54, g32p_row02_traceSegment_064_0324_0054, g32p_row02_traceSegment_064_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 216 108 108, g32p_row02_traceSegment_064_0216_0108, g32p_row02_traceSegment_064_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_064 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 0 216 216, g32p_row02_traceSegment_064_0000_0216, g32p_row02_traceSegment_064_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 432 13 14, g32p_row02_traceSegment_064_0432_0013, g32p_row02_traceSegment_064_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 459 13 14, g32p_row02_traceSegment_064_0459_0013, g32p_row02_traceSegment_064_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 432 27 27, g32p_row02_traceSegment_064_0432_0027, g32p_row02_traceSegment_064_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 486 13 14, g32p_row02_traceSegment_064_0486_0013, g32p_row02_traceSegment_064_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 513 13 14, g32p_row02_traceSegment_064_0513_0013, g32p_row02_traceSegment_064_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 486 27 27, g32p_row02_traceSegment_064_0486_0027, g32p_row02_traceSegment_064_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 432 54 54, g32p_row02_traceSegment_064_0432_0054, g32p_row02_traceSegment_064_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 540 13 14, g32p_row02_traceSegment_064_0540_0013, g32p_row02_traceSegment_064_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 567 13 14, g32p_row02_traceSegment_064_0567_0013, g32p_row02_traceSegment_064_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 540 27 27, g32p_row02_traceSegment_064_0540_0027, g32p_row02_traceSegment_064_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 594 13 14, g32p_row02_traceSegment_064_0594_0013, g32p_row02_traceSegment_064_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 621 13 14, g32p_row02_traceSegment_064_0621_0013, g32p_row02_traceSegment_064_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 594 27 27, g32p_row02_traceSegment_064_0594_0027, g32p_row02_traceSegment_064_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 540 54 54, g32p_row02_traceSegment_064_0540_0054, g32p_row02_traceSegment_064_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 432 108 108, g32p_row02_traceSegment_064_0432_0108, g32p_row02_traceSegment_064_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 648 13 14, g32p_row02_traceSegment_064_0648_0013, g32p_row02_traceSegment_064_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 675 13 14, g32p_row02_traceSegment_064_0675_0013, g32p_row02_traceSegment_064_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 648 27 27, g32p_row02_traceSegment_064_0648_0027, g32p_row02_traceSegment_064_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 702 13 14, g32p_row02_traceSegment_064_0702_0013, g32p_row02_traceSegment_064_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 729 13 14, g32p_row02_traceSegment_064_0729_0013, g32p_row02_traceSegment_064_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 702 27 27, g32p_row02_traceSegment_064_0702_0027, g32p_row02_traceSegment_064_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 648 54 54, g32p_row02_traceSegment_064_0648_0054, g32p_row02_traceSegment_064_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 756 13 14, g32p_row02_traceSegment_064_0756_0013, g32p_row02_traceSegment_064_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 783 13 14, g32p_row02_traceSegment_064_0783_0013, g32p_row02_traceSegment_064_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 756 27 27, g32p_row02_traceSegment_064_0756_0027, g32p_row02_traceSegment_064_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 810 13 14, g32p_row02_traceSegment_064_0810_0013, g32p_row02_traceSegment_064_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 837 13 14, g32p_row02_traceSegment_064_0837_0013, g32p_row02_traceSegment_064_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 810 27 27, g32p_row02_traceSegment_064_0810_0027, g32p_row02_traceSegment_064_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 756 54 54, g32p_row02_traceSegment_064_0756_0054, g32p_row02_traceSegment_064_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 648 108 108, g32p_row02_traceSegment_064_0648_0108, g32p_row02_traceSegment_064_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_064 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 432 216 216, g32p_row02_traceSegment_064_0432_0216, g32p_row02_traceSegment_064_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_064 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 0 432 432, g32p_row02_traceSegment_064_0000_0432, g32p_row02_traceSegment_064_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 864 13 14, g32p_row02_traceSegment_064_0864_0013, g32p_row02_traceSegment_064_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 891 13 14, g32p_row02_traceSegment_064_0891_0013, g32p_row02_traceSegment_064_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 864 27 27, g32p_row02_traceSegment_064_0864_0027, g32p_row02_traceSegment_064_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 918 13 14, g32p_row02_traceSegment_064_0918_0013, g32p_row02_traceSegment_064_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 945 13 14, g32p_row02_traceSegment_064_0945_0013, g32p_row02_traceSegment_064_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 918 27 27, g32p_row02_traceSegment_064_0918_0027, g32p_row02_traceSegment_064_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 864 54 54, g32p_row02_traceSegment_064_0864_0054, g32p_row02_traceSegment_064_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 972 13 14, g32p_row02_traceSegment_064_0972_0013, g32p_row02_traceSegment_064_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 999 13 14, g32p_row02_traceSegment_064_0999_0013, g32p_row02_traceSegment_064_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 972 27 27, g32p_row02_traceSegment_064_0972_0027, g32p_row02_traceSegment_064_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1026 13 14, g32p_row02_traceSegment_064_1026_0013, g32p_row02_traceSegment_064_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1053 13 14, g32p_row02_traceSegment_064_1053_0013, g32p_row02_traceSegment_064_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1026 27 27, g32p_row02_traceSegment_064_1026_0027, g32p_row02_traceSegment_064_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 972 54 54, g32p_row02_traceSegment_064_0972_0054, g32p_row02_traceSegment_064_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 864 108 108, g32p_row02_traceSegment_064_0864_0108, g32p_row02_traceSegment_064_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1080 13 14, g32p_row02_traceSegment_064_1080_0013, g32p_row02_traceSegment_064_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1107 13 14, g32p_row02_traceSegment_064_1107_0013, g32p_row02_traceSegment_064_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1080 27 27, g32p_row02_traceSegment_064_1080_0027, g32p_row02_traceSegment_064_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1134 13 14, g32p_row02_traceSegment_064_1134_0013, g32p_row02_traceSegment_064_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1161 13 14, g32p_row02_traceSegment_064_1161_0013, g32p_row02_traceSegment_064_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1134 27 27, g32p_row02_traceSegment_064_1134_0027, g32p_row02_traceSegment_064_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1080 54 54, g32p_row02_traceSegment_064_1080_0054, g32p_row02_traceSegment_064_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1188 13 14, g32p_row02_traceSegment_064_1188_0013, g32p_row02_traceSegment_064_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1215 13 14, g32p_row02_traceSegment_064_1215_0013, g32p_row02_traceSegment_064_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1188 27 27, g32p_row02_traceSegment_064_1188_0027, g32p_row02_traceSegment_064_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1242 13 14, g32p_row02_traceSegment_064_1242_0013, g32p_row02_traceSegment_064_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1269 13 14, g32p_row02_traceSegment_064_1269_0013, g32p_row02_traceSegment_064_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1242 27 27, g32p_row02_traceSegment_064_1242_0027, g32p_row02_traceSegment_064_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1188 54 54, g32p_row02_traceSegment_064_1188_0054, g32p_row02_traceSegment_064_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1080 108 108, g32p_row02_traceSegment_064_1080_0108, g32p_row02_traceSegment_064_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_064 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 864 216 216, g32p_row02_traceSegment_064_0864_0216, g32p_row02_traceSegment_064_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1296 13 14, g32p_row02_traceSegment_064_1296_0013, g32p_row02_traceSegment_064_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1323 13 14, g32p_row02_traceSegment_064_1323_0013, g32p_row02_traceSegment_064_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1296 27 27, g32p_row02_traceSegment_064_1296_0027, g32p_row02_traceSegment_064_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1350 13 14, g32p_row02_traceSegment_064_1350_0013, g32p_row02_traceSegment_064_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1377 13 14, g32p_row02_traceSegment_064_1377_0013, g32p_row02_traceSegment_064_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1350 27 27, g32p_row02_traceSegment_064_1350_0027, g32p_row02_traceSegment_064_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1296 54 54, g32p_row02_traceSegment_064_1296_0054, g32p_row02_traceSegment_064_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1404 13 14, g32p_row02_traceSegment_064_1404_0013, g32p_row02_traceSegment_064_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1431 13 14, g32p_row02_traceSegment_064_1431_0013, g32p_row02_traceSegment_064_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1404 27 27, g32p_row02_traceSegment_064_1404_0027, g32p_row02_traceSegment_064_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1458 13 14, g32p_row02_traceSegment_064_1458_0013, g32p_row02_traceSegment_064_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1485 13 14, g32p_row02_traceSegment_064_1485_0013, g32p_row02_traceSegment_064_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1458 27 27, g32p_row02_traceSegment_064_1458_0027, g32p_row02_traceSegment_064_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1404 54 54, g32p_row02_traceSegment_064_1404_0054, g32p_row02_traceSegment_064_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1296 108 108, g32p_row02_traceSegment_064_1296_0108, g32p_row02_traceSegment_064_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1512 13 14, g32p_row02_traceSegment_064_1512_0013, g32p_row02_traceSegment_064_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1539 13 14, g32p_row02_traceSegment_064_1539_0013, g32p_row02_traceSegment_064_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1512 27 27, g32p_row02_traceSegment_064_1512_0027, g32p_row02_traceSegment_064_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1566 13 14, g32p_row02_traceSegment_064_1566_0013, g32p_row02_traceSegment_064_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1593 13 14, g32p_row02_traceSegment_064_1593_0013, g32p_row02_traceSegment_064_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1566 27 27, g32p_row02_traceSegment_064_1566_0027, g32p_row02_traceSegment_064_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1512 54 54, g32p_row02_traceSegment_064_1512_0054, g32p_row02_traceSegment_064_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1620 13 14, g32p_row02_traceSegment_064_1620_0013, g32p_row02_traceSegment_064_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1647 13 14, g32p_row02_traceSegment_064_1647_0013, g32p_row02_traceSegment_064_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1620 27 27, g32p_row02_traceSegment_064_1620_0027, g32p_row02_traceSegment_064_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1674 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1687 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1674 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1674 13 14, g32p_row02_traceSegment_064_1674_0013, g32p_row02_traceSegment_064_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1701 13 14, g32p_row02_traceSegment_064_1701_0013, g32p_row02_traceSegment_064_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1674 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1674 27 27, g32p_row02_traceSegment_064_1674_0027, g32p_row02_traceSegment_064_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 1620 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1620 54 54, g32p_row02_traceSegment_064_1620_0054, g32p_row02_traceSegment_064_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 1512 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1512 108 108, g32p_row02_traceSegment_064_1512_0108, g32p_row02_traceSegment_064_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_064 1296 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1296 216 216, g32p_row02_traceSegment_064_1296_0216, g32p_row02_traceSegment_064_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_064 864 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 864 432 432, g32p_row02_traceSegment_064_0864_0432, g32p_row02_traceSegment_064_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_064 0 1728 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 0 864 864, g32p_row02_traceSegment_064_0000_0864, g32p_row02_traceSegment_064_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1728 13 14, g32p_row02_traceSegment_064_1728_0013, g32p_row02_traceSegment_064_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1755 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1755 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1755 13 14, g32p_row02_traceSegment_064_1755_0013, g32p_row02_traceSegment_064_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1728 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1728 27 27, g32p_row02_traceSegment_064_1728_0027, g32p_row02_traceSegment_064_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1782 13 14, g32p_row02_traceSegment_064_1782_0013, g32p_row02_traceSegment_064_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1809 13 14, g32p_row02_traceSegment_064_1809_0013, g32p_row02_traceSegment_064_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1782 27 27, g32p_row02_traceSegment_064_1782_0027, g32p_row02_traceSegment_064_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 1728 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1728 54 54, g32p_row02_traceSegment_064_1728_0054, g32p_row02_traceSegment_064_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1836 13 14, g32p_row02_traceSegment_064_1836_0013, g32p_row02_traceSegment_064_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1863 13 14, g32p_row02_traceSegment_064_1863_0013, g32p_row02_traceSegment_064_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1836 27 27, g32p_row02_traceSegment_064_1836_0027, g32p_row02_traceSegment_064_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1890 13 14, g32p_row02_traceSegment_064_1890_0013, g32p_row02_traceSegment_064_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1917 13 14, g32p_row02_traceSegment_064_1917_0013, g32p_row02_traceSegment_064_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1890 27 27, g32p_row02_traceSegment_064_1890_0027, g32p_row02_traceSegment_064_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1836 54 54, g32p_row02_traceSegment_064_1836_0054, g32p_row02_traceSegment_064_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 1728 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1728 108 108, g32p_row02_traceSegment_064_1728_0108, g32p_row02_traceSegment_064_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1944 13 14, g32p_row02_traceSegment_064_1944_0013, g32p_row02_traceSegment_064_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1971 13 14, g32p_row02_traceSegment_064_1971_0013, g32p_row02_traceSegment_064_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1944 27 27, g32p_row02_traceSegment_064_1944_0027, g32p_row02_traceSegment_064_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1998 13 14, g32p_row02_traceSegment_064_1998_0013, g32p_row02_traceSegment_064_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2025 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2025 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2025 13 14, g32p_row02_traceSegment_064_2025_0013, g32p_row02_traceSegment_064_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 1998 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1998 27 27, g32p_row02_traceSegment_064_1998_0027, g32p_row02_traceSegment_064_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 1944 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1944 54 54, g32p_row02_traceSegment_064_1944_0054, g32p_row02_traceSegment_064_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2052 13 14, g32p_row02_traceSegment_064_2052_0013, g32p_row02_traceSegment_064_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2079 13 14, g32p_row02_traceSegment_064_2079_0013, g32p_row02_traceSegment_064_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2052 27 27, g32p_row02_traceSegment_064_2052_0027, g32p_row02_traceSegment_064_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2106 13 14, g32p_row02_traceSegment_064_2106_0013, g32p_row02_traceSegment_064_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2133 13 14, g32p_row02_traceSegment_064_2133_0013, g32p_row02_traceSegment_064_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2106 27 27, g32p_row02_traceSegment_064_2106_0027, g32p_row02_traceSegment_064_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2052 54 54, g32p_row02_traceSegment_064_2052_0054, g32p_row02_traceSegment_064_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 1944 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1944 108 108, g32p_row02_traceSegment_064_1944_0108, g32p_row02_traceSegment_064_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_064 1728 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1728 216 216, g32p_row02_traceSegment_064_1728_0216, g32p_row02_traceSegment_064_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2160 13 14, g32p_row02_traceSegment_064_2160_0013, g32p_row02_traceSegment_064_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2187 13 14, g32p_row02_traceSegment_064_2187_0013, g32p_row02_traceSegment_064_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2160 27 27, g32p_row02_traceSegment_064_2160_0027, g32p_row02_traceSegment_064_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2214 13 14, g32p_row02_traceSegment_064_2214_0013, g32p_row02_traceSegment_064_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2241 13 14, g32p_row02_traceSegment_064_2241_0013, g32p_row02_traceSegment_064_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2214 27 27, g32p_row02_traceSegment_064_2214_0027, g32p_row02_traceSegment_064_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2160 54 54, g32p_row02_traceSegment_064_2160_0054, g32p_row02_traceSegment_064_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2268 13 14, g32p_row02_traceSegment_064_2268_0013, g32p_row02_traceSegment_064_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2295 13 14, g32p_row02_traceSegment_064_2295_0013, g32p_row02_traceSegment_064_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2268 27 27, g32p_row02_traceSegment_064_2268_0027, g32p_row02_traceSegment_064_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2322 13 14, g32p_row02_traceSegment_064_2322_0013, g32p_row02_traceSegment_064_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2349 13 14, g32p_row02_traceSegment_064_2349_0013, g32p_row02_traceSegment_064_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2322 27 27, g32p_row02_traceSegment_064_2322_0027, g32p_row02_traceSegment_064_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2268 54 54, g32p_row02_traceSegment_064_2268_0054, g32p_row02_traceSegment_064_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2160 108 108, g32p_row02_traceSegment_064_2160_0108, g32p_row02_traceSegment_064_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2376 13 14, g32p_row02_traceSegment_064_2376_0013, g32p_row02_traceSegment_064_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2403 13 14, g32p_row02_traceSegment_064_2403_0013, g32p_row02_traceSegment_064_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2376 27 27, g32p_row02_traceSegment_064_2376_0027, g32p_row02_traceSegment_064_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2430 13 14, g32p_row02_traceSegment_064_2430_0013, g32p_row02_traceSegment_064_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2457 13 14, g32p_row02_traceSegment_064_2457_0013, g32p_row02_traceSegment_064_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2430 27 27, g32p_row02_traceSegment_064_2430_0027, g32p_row02_traceSegment_064_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2376 54 54, g32p_row02_traceSegment_064_2376_0054, g32p_row02_traceSegment_064_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2484 13 14, g32p_row02_traceSegment_064_2484_0013, g32p_row02_traceSegment_064_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2511 13 14, g32p_row02_traceSegment_064_2511_0013, g32p_row02_traceSegment_064_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2484 27 27, g32p_row02_traceSegment_064_2484_0027, g32p_row02_traceSegment_064_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2538 13 14, g32p_row02_traceSegment_064_2538_0013, g32p_row02_traceSegment_064_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2565 13 14, g32p_row02_traceSegment_064_2565_0013, g32p_row02_traceSegment_064_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2538 27 27, g32p_row02_traceSegment_064_2538_0027, g32p_row02_traceSegment_064_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2484 54 54, g32p_row02_traceSegment_064_2484_0054, g32p_row02_traceSegment_064_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2376 108 108, g32p_row02_traceSegment_064_2376_0108, g32p_row02_traceSegment_064_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_064 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2160 216 216, g32p_row02_traceSegment_064_2160_0216, g32p_row02_traceSegment_064_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_064 1728 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1728 432 432, g32p_row02_traceSegment_064_1728_0432, g32p_row02_traceSegment_064_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2592 13 14, g32p_row02_traceSegment_064_2592_0013, g32p_row02_traceSegment_064_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2632 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2619 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2619 13 14, g32p_row02_traceSegment_064_2619_0013, g32p_row02_traceSegment_064_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2592 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2592 27 27, g32p_row02_traceSegment_064_2592_0027, g32p_row02_traceSegment_064_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2646 13 14, g32p_row02_traceSegment_064_2646_0013, g32p_row02_traceSegment_064_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2673 13 14, g32p_row02_traceSegment_064_2673_0013, g32p_row02_traceSegment_064_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2646 27 27, g32p_row02_traceSegment_064_2646_0027, g32p_row02_traceSegment_064_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 2592 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2592 54 54, g32p_row02_traceSegment_064_2592_0054, g32p_row02_traceSegment_064_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2700 13 14, g32p_row02_traceSegment_064_2700_0013, g32p_row02_traceSegment_064_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2727 13 14, g32p_row02_traceSegment_064_2727_0013, g32p_row02_traceSegment_064_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2700 27 27, g32p_row02_traceSegment_064_2700_0027, g32p_row02_traceSegment_064_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2754 13 14, g32p_row02_traceSegment_064_2754_0013, g32p_row02_traceSegment_064_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2781 13 14, g32p_row02_traceSegment_064_2781_0013, g32p_row02_traceSegment_064_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2754 27 27, g32p_row02_traceSegment_064_2754_0027, g32p_row02_traceSegment_064_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2700 54 54, g32p_row02_traceSegment_064_2700_0054, g32p_row02_traceSegment_064_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 2592 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2592 108 108, g32p_row02_traceSegment_064_2592_0108, g32p_row02_traceSegment_064_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2808 13 14, g32p_row02_traceSegment_064_2808_0013, g32p_row02_traceSegment_064_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2835 13 14, g32p_row02_traceSegment_064_2835_0013, g32p_row02_traceSegment_064_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2808 27 27, g32p_row02_traceSegment_064_2808_0027, g32p_row02_traceSegment_064_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2875 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2862 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2862 13 14, g32p_row02_traceSegment_064_2862_0013, g32p_row02_traceSegment_064_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2889 13 14, g32p_row02_traceSegment_064_2889_0013, g32p_row02_traceSegment_064_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2862 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2862 27 27, g32p_row02_traceSegment_064_2862_0027, g32p_row02_traceSegment_064_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 2808 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2808 54 54, g32p_row02_traceSegment_064_2808_0054, g32p_row02_traceSegment_064_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2916 13 14, g32p_row02_traceSegment_064_2916_0013, g32p_row02_traceSegment_064_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2956 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2943 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2943 13 14, g32p_row02_traceSegment_064_2943_0013, g32p_row02_traceSegment_064_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2916 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2916 27 27, g32p_row02_traceSegment_064_2916_0027, g32p_row02_traceSegment_064_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2970 13 14, g32p_row02_traceSegment_064_2970_0013, g32p_row02_traceSegment_064_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2997 13 14, g32p_row02_traceSegment_064_2997_0013, g32p_row02_traceSegment_064_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2970 27 27, g32p_row02_traceSegment_064_2970_0027, g32p_row02_traceSegment_064_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 2916 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2916 54 54, g32p_row02_traceSegment_064_2916_0054, g32p_row02_traceSegment_064_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 2808 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2808 108 108, g32p_row02_traceSegment_064_2808_0108, g32p_row02_traceSegment_064_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_064 2592 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2592 216 216, g32p_row02_traceSegment_064_2592_0216, g32p_row02_traceSegment_064_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3024 13 14, g32p_row02_traceSegment_064_3024_0013, g32p_row02_traceSegment_064_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3051 13 14, g32p_row02_traceSegment_064_3051_0013, g32p_row02_traceSegment_064_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3024 27 27, g32p_row02_traceSegment_064_3024_0027, g32p_row02_traceSegment_064_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3078 13 14, g32p_row02_traceSegment_064_3078_0013, g32p_row02_traceSegment_064_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3105 13 14, g32p_row02_traceSegment_064_3105_0013, g32p_row02_traceSegment_064_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3078 27 27, g32p_row02_traceSegment_064_3078_0027, g32p_row02_traceSegment_064_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3024 54 54, g32p_row02_traceSegment_064_3024_0054, g32p_row02_traceSegment_064_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3132 13 14, g32p_row02_traceSegment_064_3132_0013, g32p_row02_traceSegment_064_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3159 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3159 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3159 13 14, g32p_row02_traceSegment_064_3159_0013, g32p_row02_traceSegment_064_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 3132 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3132 27 27, g32p_row02_traceSegment_064_3132_0027, g32p_row02_traceSegment_064_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3186 13 14, g32p_row02_traceSegment_064_3186_0013, g32p_row02_traceSegment_064_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3213 13 14, g32p_row02_traceSegment_064_3213_0013, g32p_row02_traceSegment_064_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3186 27 27, g32p_row02_traceSegment_064_3186_0027, g32p_row02_traceSegment_064_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 3132 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3132 54 54, g32p_row02_traceSegment_064_3132_0054, g32p_row02_traceSegment_064_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 3024 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3024 108 108, g32p_row02_traceSegment_064_3024_0108, g32p_row02_traceSegment_064_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3240 13 14, g32p_row02_traceSegment_064_3240_0013, g32p_row02_traceSegment_064_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3267 13 14, g32p_row02_traceSegment_064_3267_0013, g32p_row02_traceSegment_064_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3240 27 27, g32p_row02_traceSegment_064_3240_0027, g32p_row02_traceSegment_064_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3294 13 14, g32p_row02_traceSegment_064_3294_0013, g32p_row02_traceSegment_064_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3321 13 14, g32p_row02_traceSegment_064_3321_0013, g32p_row02_traceSegment_064_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3294 27 27, g32p_row02_traceSegment_064_3294_0027, g32p_row02_traceSegment_064_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3240 54 54, g32p_row02_traceSegment_064_3240_0054, g32p_row02_traceSegment_064_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3348 13 14, g32p_row02_traceSegment_064_3348_0013, g32p_row02_traceSegment_064_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3375 13 14, g32p_row02_traceSegment_064_3375_0013, g32p_row02_traceSegment_064_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3348 27 27, g32p_row02_traceSegment_064_3348_0027, g32p_row02_traceSegment_064_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3402 13 14, g32p_row02_traceSegment_064_3402_0013, g32p_row02_traceSegment_064_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_064 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_064 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_064_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_064 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3429 13 14, g32p_row02_traceSegment_064_3429_0013, g32p_row02_traceSegment_064_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_064 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3402 27 27, g32p_row02_traceSegment_064_3402_0027, g32p_row02_traceSegment_064_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_064 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3348 54 54, g32p_row02_traceSegment_064_3348_0054, g32p_row02_traceSegment_064_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_064 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3240 108 108, g32p_row02_traceSegment_064_3240_0108, g32p_row02_traceSegment_064_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_064_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_064 3024 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 3024 216 216, g32p_row02_traceSegment_064_3024_0216, g32p_row02_traceSegment_064_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_064_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_064 2592 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 2592 432 432, g32p_row02_traceSegment_064_2592_0432, g32p_row02_traceSegment_064_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_064_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_064 1728 1728 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 1728 864 864, g32p_row02_traceSegment_064_1728_0864, g32p_row02_traceSegment_064_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_064_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_064 0 3456 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_064 0 1728 1728, g32p_row02_traceSegment_064_0000_1728, g32p_row02_traceSegment_064_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 64 = [0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_064_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_065 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 65 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_065_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 13 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 0 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 0 13 14, g32p_row02_traceSegment_065_0000_0013, g32p_row02_traceSegment_065_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 27 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 40 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 27 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 27 13 14, g32p_row02_traceSegment_065_0027_0013, g32p_row02_traceSegment_065_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 0 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 0 27 27, g32p_row02_traceSegment_065_0000_0027, g32p_row02_traceSegment_065_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 67 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 54 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 54 13 14, g32p_row02_traceSegment_065_0054_0013, g32p_row02_traceSegment_065_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 81 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 81 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 81 13 14, g32p_row02_traceSegment_065_0081_0013, g32p_row02_traceSegment_065_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 54 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 54 27 27, g32p_row02_traceSegment_065_0054_0027, g32p_row02_traceSegment_065_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 0 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 0 54 54, g32p_row02_traceSegment_065_0000_0054, g32p_row02_traceSegment_065_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 108 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 108 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 108 13 14, g32p_row02_traceSegment_065_0108_0013, g32p_row02_traceSegment_065_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 135 13 14, g32p_row02_traceSegment_065_0135_0013, g32p_row02_traceSegment_065_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 108 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 108 27 27, g32p_row02_traceSegment_065_0108_0027, g32p_row02_traceSegment_065_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 175 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 162 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 162 13 14, g32p_row02_traceSegment_065_0162_0013, g32p_row02_traceSegment_065_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 189 13 14, g32p_row02_traceSegment_065_0189_0013, g32p_row02_traceSegment_065_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 162 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 162 27 27, g32p_row02_traceSegment_065_0162_0027, g32p_row02_traceSegment_065_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 108 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 108 54 54, g32p_row02_traceSegment_065_0108_0054, g32p_row02_traceSegment_065_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 0 216 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 0 108 108, g32p_row02_traceSegment_065_0000_0108, g32p_row02_traceSegment_065_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 216 13 14, g32p_row02_traceSegment_065_0216_0013, g32p_row02_traceSegment_065_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 243 13 14, g32p_row02_traceSegment_065_0243_0013, g32p_row02_traceSegment_065_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 216 27 27, g32p_row02_traceSegment_065_0216_0027, g32p_row02_traceSegment_065_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 270 13 14, g32p_row02_traceSegment_065_0270_0013, g32p_row02_traceSegment_065_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 297 13 14, g32p_row02_traceSegment_065_0297_0013, g32p_row02_traceSegment_065_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 270 27 27, g32p_row02_traceSegment_065_0270_0027, g32p_row02_traceSegment_065_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 216 54 54, g32p_row02_traceSegment_065_0216_0054, g32p_row02_traceSegment_065_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 324 13 14, g32p_row02_traceSegment_065_0324_0013, g32p_row02_traceSegment_065_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 351 13 14, g32p_row02_traceSegment_065_0351_0013, g32p_row02_traceSegment_065_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 324 27 27, g32p_row02_traceSegment_065_0324_0027, g32p_row02_traceSegment_065_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 378 13 14, g32p_row02_traceSegment_065_0378_0013, g32p_row02_traceSegment_065_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 405 13 14, g32p_row02_traceSegment_065_0405_0013, g32p_row02_traceSegment_065_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 378 27 27, g32p_row02_traceSegment_065_0378_0027, g32p_row02_traceSegment_065_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 324 54 54, g32p_row02_traceSegment_065_0324_0054, g32p_row02_traceSegment_065_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 216 108 108, g32p_row02_traceSegment_065_0216_0108, g32p_row02_traceSegment_065_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_065 0 432 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 0 216 216, g32p_row02_traceSegment_065_0000_0216, g32p_row02_traceSegment_065_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 432 13 14, g32p_row02_traceSegment_065_0432_0013, g32p_row02_traceSegment_065_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 459 13 14, g32p_row02_traceSegment_065_0459_0013, g32p_row02_traceSegment_065_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 432 27 27, g32p_row02_traceSegment_065_0432_0027, g32p_row02_traceSegment_065_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 486 13 14, g32p_row02_traceSegment_065_0486_0013, g32p_row02_traceSegment_065_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 513 13 14, g32p_row02_traceSegment_065_0513_0013, g32p_row02_traceSegment_065_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 486 27 27, g32p_row02_traceSegment_065_0486_0027, g32p_row02_traceSegment_065_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 432 54 54, g32p_row02_traceSegment_065_0432_0054, g32p_row02_traceSegment_065_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 540 13 14, g32p_row02_traceSegment_065_0540_0013, g32p_row02_traceSegment_065_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 567 13 14, g32p_row02_traceSegment_065_0567_0013, g32p_row02_traceSegment_065_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 540 27 27, g32p_row02_traceSegment_065_0540_0027, g32p_row02_traceSegment_065_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 594 13 14, g32p_row02_traceSegment_065_0594_0013, g32p_row02_traceSegment_065_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 621 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 634 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 621 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 621 13 14, g32p_row02_traceSegment_065_0621_0013, g32p_row02_traceSegment_065_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 594 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 594 27 27, g32p_row02_traceSegment_065_0594_0027, g32p_row02_traceSegment_065_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 540 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 540 54 54, g32p_row02_traceSegment_065_0540_0054, g32p_row02_traceSegment_065_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 432 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 432 108 108, g32p_row02_traceSegment_065_0432_0108, g32p_row02_traceSegment_065_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 648 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 661 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 648 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 648 13 14, g32p_row02_traceSegment_065_0648_0013, g32p_row02_traceSegment_065_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 675 13 14, g32p_row02_traceSegment_065_0675_0013, g32p_row02_traceSegment_065_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 648 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 648 27 27, g32p_row02_traceSegment_065_0648_0027, g32p_row02_traceSegment_065_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 702 13 14, g32p_row02_traceSegment_065_0702_0013, g32p_row02_traceSegment_065_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 729 13 14, g32p_row02_traceSegment_065_0729_0013, g32p_row02_traceSegment_065_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 702 27 27, g32p_row02_traceSegment_065_0702_0027, g32p_row02_traceSegment_065_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 648 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 648 54 54, g32p_row02_traceSegment_065_0648_0054, g32p_row02_traceSegment_065_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 756 13 14, g32p_row02_traceSegment_065_0756_0013, g32p_row02_traceSegment_065_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 783 13 14, g32p_row02_traceSegment_065_0783_0013, g32p_row02_traceSegment_065_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 756 27 27, g32p_row02_traceSegment_065_0756_0027, g32p_row02_traceSegment_065_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 810 13 14, g32p_row02_traceSegment_065_0810_0013, g32p_row02_traceSegment_065_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 837 13 14, g32p_row02_traceSegment_065_0837_0013, g32p_row02_traceSegment_065_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 810 27 27, g32p_row02_traceSegment_065_0810_0027, g32p_row02_traceSegment_065_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 756 54 54, g32p_row02_traceSegment_065_0756_0054, g32p_row02_traceSegment_065_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 648 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 648 108 108, g32p_row02_traceSegment_065_0648_0108, g32p_row02_traceSegment_065_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_065 432 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 432 216 216, g32p_row02_traceSegment_065_0432_0216, g32p_row02_traceSegment_065_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_065 0 864 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 0 432 432, g32p_row02_traceSegment_065_0000_0432, g32p_row02_traceSegment_065_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 864 13 14, g32p_row02_traceSegment_065_0864_0013, g32p_row02_traceSegment_065_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 891 13 14, g32p_row02_traceSegment_065_0891_0013, g32p_row02_traceSegment_065_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 864 27 27, g32p_row02_traceSegment_065_0864_0027, g32p_row02_traceSegment_065_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 918 13 14, g32p_row02_traceSegment_065_0918_0013, g32p_row02_traceSegment_065_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 945 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 945 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 945 13 14, g32p_row02_traceSegment_065_0945_0013, g32p_row02_traceSegment_065_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 918 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 918 27 27, g32p_row02_traceSegment_065_0918_0027, g32p_row02_traceSegment_065_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 864 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 864 54 54, g32p_row02_traceSegment_065_0864_0054, g32p_row02_traceSegment_065_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 972 13 14, g32p_row02_traceSegment_065_0972_0013, g32p_row02_traceSegment_065_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 999 13 14, g32p_row02_traceSegment_065_0999_0013, g32p_row02_traceSegment_065_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 972 27 27, g32p_row02_traceSegment_065_0972_0027, g32p_row02_traceSegment_065_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1026 13 14, g32p_row02_traceSegment_065_1026_0013, g32p_row02_traceSegment_065_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1053 13 14, g32p_row02_traceSegment_065_1053_0013, g32p_row02_traceSegment_065_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1026 27 27, g32p_row02_traceSegment_065_1026_0027, g32p_row02_traceSegment_065_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 972 54 54, g32p_row02_traceSegment_065_0972_0054, g32p_row02_traceSegment_065_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 864 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 864 108 108, g32p_row02_traceSegment_065_0864_0108, g32p_row02_traceSegment_065_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1080 13 14, g32p_row02_traceSegment_065_1080_0013, g32p_row02_traceSegment_065_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1107 13 14, g32p_row02_traceSegment_065_1107_0013, g32p_row02_traceSegment_065_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1080 27 27, g32p_row02_traceSegment_065_1080_0027, g32p_row02_traceSegment_065_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1134 13 14, g32p_row02_traceSegment_065_1134_0013, g32p_row02_traceSegment_065_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1161 13 14, g32p_row02_traceSegment_065_1161_0013, g32p_row02_traceSegment_065_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1134 27 27, g32p_row02_traceSegment_065_1134_0027, g32p_row02_traceSegment_065_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1080 54 54, g32p_row02_traceSegment_065_1080_0054, g32p_row02_traceSegment_065_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1188 13 14, g32p_row02_traceSegment_065_1188_0013, g32p_row02_traceSegment_065_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1215 13 14, g32p_row02_traceSegment_065_1215_0013, g32p_row02_traceSegment_065_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1188 27 27, g32p_row02_traceSegment_065_1188_0027, g32p_row02_traceSegment_065_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1242 13 14, g32p_row02_traceSegment_065_1242_0013, g32p_row02_traceSegment_065_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1269 13 14, g32p_row02_traceSegment_065_1269_0013, g32p_row02_traceSegment_065_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1242 27 27, g32p_row02_traceSegment_065_1242_0027, g32p_row02_traceSegment_065_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1188 54 54, g32p_row02_traceSegment_065_1188_0054, g32p_row02_traceSegment_065_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1080 108 108, g32p_row02_traceSegment_065_1080_0108, g32p_row02_traceSegment_065_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_065 864 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 864 216 216, g32p_row02_traceSegment_065_0864_0216, g32p_row02_traceSegment_065_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1296 13 14, g32p_row02_traceSegment_065_1296_0013, g32p_row02_traceSegment_065_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1336 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1323 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1323 13 14, g32p_row02_traceSegment_065_1323_0013, g32p_row02_traceSegment_065_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1296 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1296 27 27, g32p_row02_traceSegment_065_1296_0027, g32p_row02_traceSegment_065_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1363 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1350 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1350 13 14, g32p_row02_traceSegment_065_1350_0013, g32p_row02_traceSegment_065_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1390 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1377 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1377 13 14, g32p_row02_traceSegment_065_1377_0013, g32p_row02_traceSegment_065_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1350 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1350 27 27, g32p_row02_traceSegment_065_1350_0027, g32p_row02_traceSegment_065_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 1296 108 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1296 54 54, g32p_row02_traceSegment_065_1296_0054, g32p_row02_traceSegment_065_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1404 13 14, g32p_row02_traceSegment_065_1404_0013, g32p_row02_traceSegment_065_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1444 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1431 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1431 13 14, g32p_row02_traceSegment_065_1431_0013, g32p_row02_traceSegment_065_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1404 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1404 27 27, g32p_row02_traceSegment_065_1404_0027, g32p_row02_traceSegment_065_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1458 13 14, g32p_row02_traceSegment_065_1458_0013, g32p_row02_traceSegment_065_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1485 13 14, g32p_row02_traceSegment_065_1485_0013, g32p_row02_traceSegment_065_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1458 27 27, g32p_row02_traceSegment_065_1458_0027, g32p_row02_traceSegment_065_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 1404 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1404 54 54, g32p_row02_traceSegment_065_1404_0054, g32p_row02_traceSegment_065_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 1296 216 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1296 108 108, g32p_row02_traceSegment_065_1296_0108, g32p_row02_traceSegment_065_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1512 13 14, g32p_row02_traceSegment_065_1512_0013, g32p_row02_traceSegment_065_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1539 13 14, g32p_row02_traceSegment_065_1539_0013, g32p_row02_traceSegment_065_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1512 27 27, g32p_row02_traceSegment_065_1512_0027, g32p_row02_traceSegment_065_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1566 13 14, g32p_row02_traceSegment_065_1566_0013, g32p_row02_traceSegment_065_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1593 13 14, g32p_row02_traceSegment_065_1593_0013, g32p_row02_traceSegment_065_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1566 27 27, g32p_row02_traceSegment_065_1566_0027, g32p_row02_traceSegment_065_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1512 54 54, g32p_row02_traceSegment_065_1512_0054, g32p_row02_traceSegment_065_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1620 13 14, g32p_row02_traceSegment_065_1620_0013, g32p_row02_traceSegment_065_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1647 13 14, g32p_row02_traceSegment_065_1647_0013, g32p_row02_traceSegment_065_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1620 27 27, g32p_row02_traceSegment_065_1620_0027, g32p_row02_traceSegment_065_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1674 13 14, g32p_row02_traceSegment_065_1674_0013, g32p_row02_traceSegment_065_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1701 13 14, g32p_row02_traceSegment_065_1701_0013, g32p_row02_traceSegment_065_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1674 27 27, g32p_row02_traceSegment_065_1674_0027, g32p_row02_traceSegment_065_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1620 54 54, g32p_row02_traceSegment_065_1620_0054, g32p_row02_traceSegment_065_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1512 108 108, g32p_row02_traceSegment_065_1512_0108, g32p_row02_traceSegment_065_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_065 1296 432 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1296 216 216, g32p_row02_traceSegment_065_1296_0216, g32p_row02_traceSegment_065_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_065 864 864 = [0, 8, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 864 432 432, g32p_row02_traceSegment_065_0864_0432, g32p_row02_traceSegment_065_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_065 0 1728 = [0, 24, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 0 864 864, g32p_row02_traceSegment_065_0000_0864, g32p_row02_traceSegment_065_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1728 13 14, g32p_row02_traceSegment_065_1728_0013, g32p_row02_traceSegment_065_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1755 13 14, g32p_row02_traceSegment_065_1755_0013, g32p_row02_traceSegment_065_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1728 27 27, g32p_row02_traceSegment_065_1728_0027, g32p_row02_traceSegment_065_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1782 13 14, g32p_row02_traceSegment_065_1782_0013, g32p_row02_traceSegment_065_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1809 13 14, g32p_row02_traceSegment_065_1809_0013, g32p_row02_traceSegment_065_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1782 27 27, g32p_row02_traceSegment_065_1782_0027, g32p_row02_traceSegment_065_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1728 54 54, g32p_row02_traceSegment_065_1728_0054, g32p_row02_traceSegment_065_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1836 13 14, g32p_row02_traceSegment_065_1836_0013, g32p_row02_traceSegment_065_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1863 13 14, g32p_row02_traceSegment_065_1863_0013, g32p_row02_traceSegment_065_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1836 27 27, g32p_row02_traceSegment_065_1836_0027, g32p_row02_traceSegment_065_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1890 13 14, g32p_row02_traceSegment_065_1890_0013, g32p_row02_traceSegment_065_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1917 13 14, g32p_row02_traceSegment_065_1917_0013, g32p_row02_traceSegment_065_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1890 27 27, g32p_row02_traceSegment_065_1890_0027, g32p_row02_traceSegment_065_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1836 54 54, g32p_row02_traceSegment_065_1836_0054, g32p_row02_traceSegment_065_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1728 108 108, g32p_row02_traceSegment_065_1728_0108, g32p_row02_traceSegment_065_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1944 13 14, g32p_row02_traceSegment_065_1944_0013, g32p_row02_traceSegment_065_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1971 13 14, g32p_row02_traceSegment_065_1971_0013, g32p_row02_traceSegment_065_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1944 27 27, g32p_row02_traceSegment_065_1944_0027, g32p_row02_traceSegment_065_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1998 13 14, g32p_row02_traceSegment_065_1998_0013, g32p_row02_traceSegment_065_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2025 13 14, g32p_row02_traceSegment_065_2025_0013, g32p_row02_traceSegment_065_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1998 27 27, g32p_row02_traceSegment_065_1998_0027, g32p_row02_traceSegment_065_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1944 54 54, g32p_row02_traceSegment_065_1944_0054, g32p_row02_traceSegment_065_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2052 13 14, g32p_row02_traceSegment_065_2052_0013, g32p_row02_traceSegment_065_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2079 13 14, g32p_row02_traceSegment_065_2079_0013, g32p_row02_traceSegment_065_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2052 27 27, g32p_row02_traceSegment_065_2052_0027, g32p_row02_traceSegment_065_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2106 13 14, g32p_row02_traceSegment_065_2106_0013, g32p_row02_traceSegment_065_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2133 13 14, g32p_row02_traceSegment_065_2133_0013, g32p_row02_traceSegment_065_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2106 27 27, g32p_row02_traceSegment_065_2106_0027, g32p_row02_traceSegment_065_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2052 54 54, g32p_row02_traceSegment_065_2052_0054, g32p_row02_traceSegment_065_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1944 108 108, g32p_row02_traceSegment_065_1944_0108, g32p_row02_traceSegment_065_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_065 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1728 216 216, g32p_row02_traceSegment_065_1728_0216, g32p_row02_traceSegment_065_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2160 13 14, g32p_row02_traceSegment_065_2160_0013, g32p_row02_traceSegment_065_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2187 13 14, g32p_row02_traceSegment_065_2187_0013, g32p_row02_traceSegment_065_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2160 27 27, g32p_row02_traceSegment_065_2160_0027, g32p_row02_traceSegment_065_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2214 13 14, g32p_row02_traceSegment_065_2214_0013, g32p_row02_traceSegment_065_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2241 13 14, g32p_row02_traceSegment_065_2241_0013, g32p_row02_traceSegment_065_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2214 27 27, g32p_row02_traceSegment_065_2214_0027, g32p_row02_traceSegment_065_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2160 54 54, g32p_row02_traceSegment_065_2160_0054, g32p_row02_traceSegment_065_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2268 13 14, g32p_row02_traceSegment_065_2268_0013, g32p_row02_traceSegment_065_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2295 13 14, g32p_row02_traceSegment_065_2295_0013, g32p_row02_traceSegment_065_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2268 27 27, g32p_row02_traceSegment_065_2268_0027, g32p_row02_traceSegment_065_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2322 13 14, g32p_row02_traceSegment_065_2322_0013, g32p_row02_traceSegment_065_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2349 13 14, g32p_row02_traceSegment_065_2349_0013, g32p_row02_traceSegment_065_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2322 27 27, g32p_row02_traceSegment_065_2322_0027, g32p_row02_traceSegment_065_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2268 54 54, g32p_row02_traceSegment_065_2268_0054, g32p_row02_traceSegment_065_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2160 108 108, g32p_row02_traceSegment_065_2160_0108, g32p_row02_traceSegment_065_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2376 13 14, g32p_row02_traceSegment_065_2376_0013, g32p_row02_traceSegment_065_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2403 13 14, g32p_row02_traceSegment_065_2403_0013, g32p_row02_traceSegment_065_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2376 27 27, g32p_row02_traceSegment_065_2376_0027, g32p_row02_traceSegment_065_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2430 13 14, g32p_row02_traceSegment_065_2430_0013, g32p_row02_traceSegment_065_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2457 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2457 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2457 13 14, g32p_row02_traceSegment_065_2457_0013, g32p_row02_traceSegment_065_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2430 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2430 27 27, g32p_row02_traceSegment_065_2430_0027, g32p_row02_traceSegment_065_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 2376 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2376 54 54, g32p_row02_traceSegment_065_2376_0054, g32p_row02_traceSegment_065_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2484 13 14, g32p_row02_traceSegment_065_2484_0013, g32p_row02_traceSegment_065_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2511 13 14, g32p_row02_traceSegment_065_2511_0013, g32p_row02_traceSegment_065_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2484 27 27, g32p_row02_traceSegment_065_2484_0027, g32p_row02_traceSegment_065_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2538 13 14, g32p_row02_traceSegment_065_2538_0013, g32p_row02_traceSegment_065_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2565 13 14, g32p_row02_traceSegment_065_2565_0013, g32p_row02_traceSegment_065_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2538 27 27, g32p_row02_traceSegment_065_2538_0027, g32p_row02_traceSegment_065_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2484 54 54, g32p_row02_traceSegment_065_2484_0054, g32p_row02_traceSegment_065_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 2376 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2376 108 108, g32p_row02_traceSegment_065_2376_0108, g32p_row02_traceSegment_065_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_065 2160 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2160 216 216, g32p_row02_traceSegment_065_2160_0216, g32p_row02_traceSegment_065_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_065 1728 864 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1728 432 432, g32p_row02_traceSegment_065_1728_0432, g32p_row02_traceSegment_065_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2592 13 14, g32p_row02_traceSegment_065_2592_0013, g32p_row02_traceSegment_065_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2619 13 14, g32p_row02_traceSegment_065_2619_0013, g32p_row02_traceSegment_065_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2592 27 27, g32p_row02_traceSegment_065_2592_0027, g32p_row02_traceSegment_065_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2646 13 14, g32p_row02_traceSegment_065_2646_0013, g32p_row02_traceSegment_065_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2673 13 14, g32p_row02_traceSegment_065_2673_0013, g32p_row02_traceSegment_065_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2646 27 27, g32p_row02_traceSegment_065_2646_0027, g32p_row02_traceSegment_065_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2592 54 54, g32p_row02_traceSegment_065_2592_0054, g32p_row02_traceSegment_065_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2700 13 14, g32p_row02_traceSegment_065_2700_0013, g32p_row02_traceSegment_065_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2727 13 14, g32p_row02_traceSegment_065_2727_0013, g32p_row02_traceSegment_065_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2700 27 27, g32p_row02_traceSegment_065_2700_0027, g32p_row02_traceSegment_065_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2754 13 14, g32p_row02_traceSegment_065_2754_0013, g32p_row02_traceSegment_065_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2781 13 14, g32p_row02_traceSegment_065_2781_0013, g32p_row02_traceSegment_065_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2754 27 27, g32p_row02_traceSegment_065_2754_0027, g32p_row02_traceSegment_065_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2700 54 54, g32p_row02_traceSegment_065_2700_0054, g32p_row02_traceSegment_065_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2592 108 108, g32p_row02_traceSegment_065_2592_0108, g32p_row02_traceSegment_065_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2808 13 14, g32p_row02_traceSegment_065_2808_0013, g32p_row02_traceSegment_065_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2835 13 14, g32p_row02_traceSegment_065_2835_0013, g32p_row02_traceSegment_065_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2808 27 27, g32p_row02_traceSegment_065_2808_0027, g32p_row02_traceSegment_065_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2862 13 14, g32p_row02_traceSegment_065_2862_0013, g32p_row02_traceSegment_065_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2889 13 14, g32p_row02_traceSegment_065_2889_0013, g32p_row02_traceSegment_065_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2862 27 27, g32p_row02_traceSegment_065_2862_0027, g32p_row02_traceSegment_065_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2808 54 54, g32p_row02_traceSegment_065_2808_0054, g32p_row02_traceSegment_065_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2916 13 14, g32p_row02_traceSegment_065_2916_0013, g32p_row02_traceSegment_065_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2943 13 14, g32p_row02_traceSegment_065_2943_0013, g32p_row02_traceSegment_065_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2916 27 27, g32p_row02_traceSegment_065_2916_0027, g32p_row02_traceSegment_065_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2970 13 14, g32p_row02_traceSegment_065_2970_0013, g32p_row02_traceSegment_065_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2997 13 14, g32p_row02_traceSegment_065_2997_0013, g32p_row02_traceSegment_065_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2970 27 27, g32p_row02_traceSegment_065_2970_0027, g32p_row02_traceSegment_065_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2916 54 54, g32p_row02_traceSegment_065_2916_0054, g32p_row02_traceSegment_065_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2808 108 108, g32p_row02_traceSegment_065_2808_0108, g32p_row02_traceSegment_065_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_065 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2592 216 216, g32p_row02_traceSegment_065_2592_0216, g32p_row02_traceSegment_065_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3024 13 14, g32p_row02_traceSegment_065_3024_0013, g32p_row02_traceSegment_065_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3051 13 14, g32p_row02_traceSegment_065_3051_0013, g32p_row02_traceSegment_065_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3024 27 27, g32p_row02_traceSegment_065_3024_0027, g32p_row02_traceSegment_065_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3078 13 14, g32p_row02_traceSegment_065_3078_0013, g32p_row02_traceSegment_065_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3105 13 14, g32p_row02_traceSegment_065_3105_0013, g32p_row02_traceSegment_065_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3078 27 27, g32p_row02_traceSegment_065_3078_0027, g32p_row02_traceSegment_065_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3024 54 54, g32p_row02_traceSegment_065_3024_0054, g32p_row02_traceSegment_065_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3132 13 14, g32p_row02_traceSegment_065_3132_0013, g32p_row02_traceSegment_065_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3159 13 14, g32p_row02_traceSegment_065_3159_0013, g32p_row02_traceSegment_065_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3132 27 27, g32p_row02_traceSegment_065_3132_0027, g32p_row02_traceSegment_065_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3186 13 14, g32p_row02_traceSegment_065_3186_0013, g32p_row02_traceSegment_065_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3213 13 14, g32p_row02_traceSegment_065_3213_0013, g32p_row02_traceSegment_065_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3186 27 27, g32p_row02_traceSegment_065_3186_0027, g32p_row02_traceSegment_065_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3132 54 54, g32p_row02_traceSegment_065_3132_0054, g32p_row02_traceSegment_065_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3024 108 108, g32p_row02_traceSegment_065_3024_0108, g32p_row02_traceSegment_065_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3240 13 14, g32p_row02_traceSegment_065_3240_0013, g32p_row02_traceSegment_065_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3267 13 14, g32p_row02_traceSegment_065_3267_0013, g32p_row02_traceSegment_065_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3240 27 27, g32p_row02_traceSegment_065_3240_0027, g32p_row02_traceSegment_065_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3294 13 14, g32p_row02_traceSegment_065_3294_0013, g32p_row02_traceSegment_065_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3321 13 14, g32p_row02_traceSegment_065_3321_0013, g32p_row02_traceSegment_065_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3294 27 27, g32p_row02_traceSegment_065_3294_0027, g32p_row02_traceSegment_065_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3240 54 54, g32p_row02_traceSegment_065_3240_0054, g32p_row02_traceSegment_065_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3348 13 14, g32p_row02_traceSegment_065_3348_0013, g32p_row02_traceSegment_065_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3375 13 14, g32p_row02_traceSegment_065_3375_0013, g32p_row02_traceSegment_065_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3348 27 27, g32p_row02_traceSegment_065_3348_0027, g32p_row02_traceSegment_065_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3402 13 14, g32p_row02_traceSegment_065_3402_0013, g32p_row02_traceSegment_065_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_065 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_065 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_065_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_065 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3429 13 14, g32p_row02_traceSegment_065_3429_0013, g32p_row02_traceSegment_065_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_065 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3402 27 27, g32p_row02_traceSegment_065_3402_0027, g32p_row02_traceSegment_065_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_065 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3348 54 54, g32p_row02_traceSegment_065_3348_0054, g32p_row02_traceSegment_065_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_065 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3240 108 108, g32p_row02_traceSegment_065_3240_0108, g32p_row02_traceSegment_065_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_065_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_065 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 3024 216 216, g32p_row02_traceSegment_065_3024_0216, g32p_row02_traceSegment_065_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_065_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_065 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 2592 432 432, g32p_row02_traceSegment_065_2592_0432, g32p_row02_traceSegment_065_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_065_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_065 1728 1728 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 1728 864 864, g32p_row02_traceSegment_065_1728_0864, g32p_row02_traceSegment_065_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_065_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_065 0 3456 = [0, 24, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_065 0 1728 1728, g32p_row02_traceSegment_065_0000_1728, g32p_row02_traceSegment_065_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 65 = [0, 24, 0, 0, 2] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_065_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_066 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 66 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_066_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 0 13 14, g32p_row02_traceSegment_066_0000_0013, g32p_row02_traceSegment_066_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 27 13 14, g32p_row02_traceSegment_066_0027_0013, g32p_row02_traceSegment_066_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 0 27 27, g32p_row02_traceSegment_066_0000_0027, g32p_row02_traceSegment_066_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 54 13 14, g32p_row02_traceSegment_066_0054_0013, g32p_row02_traceSegment_066_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 81 13 14, g32p_row02_traceSegment_066_0081_0013, g32p_row02_traceSegment_066_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 54 27 27, g32p_row02_traceSegment_066_0054_0027, g32p_row02_traceSegment_066_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 0 54 54, g32p_row02_traceSegment_066_0000_0054, g32p_row02_traceSegment_066_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 108 13 14, g32p_row02_traceSegment_066_0108_0013, g32p_row02_traceSegment_066_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 135 13 14, g32p_row02_traceSegment_066_0135_0013, g32p_row02_traceSegment_066_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 108 27 27, g32p_row02_traceSegment_066_0108_0027, g32p_row02_traceSegment_066_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 162 13 14, g32p_row02_traceSegment_066_0162_0013, g32p_row02_traceSegment_066_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 189 13 14, g32p_row02_traceSegment_066_0189_0013, g32p_row02_traceSegment_066_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 162 27 27, g32p_row02_traceSegment_066_0162_0027, g32p_row02_traceSegment_066_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 108 54 54, g32p_row02_traceSegment_066_0108_0054, g32p_row02_traceSegment_066_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 0 108 108, g32p_row02_traceSegment_066_0000_0108, g32p_row02_traceSegment_066_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 216 13 14, g32p_row02_traceSegment_066_0216_0013, g32p_row02_traceSegment_066_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 243 13 14, g32p_row02_traceSegment_066_0243_0013, g32p_row02_traceSegment_066_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 216 27 27, g32p_row02_traceSegment_066_0216_0027, g32p_row02_traceSegment_066_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 270 13 14, g32p_row02_traceSegment_066_0270_0013, g32p_row02_traceSegment_066_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 297 13 14, g32p_row02_traceSegment_066_0297_0013, g32p_row02_traceSegment_066_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 270 27 27, g32p_row02_traceSegment_066_0270_0027, g32p_row02_traceSegment_066_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 216 54 54, g32p_row02_traceSegment_066_0216_0054, g32p_row02_traceSegment_066_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 324 13 14, g32p_row02_traceSegment_066_0324_0013, g32p_row02_traceSegment_066_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 351 13 14, g32p_row02_traceSegment_066_0351_0013, g32p_row02_traceSegment_066_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 324 27 27, g32p_row02_traceSegment_066_0324_0027, g32p_row02_traceSegment_066_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 378 13 14, g32p_row02_traceSegment_066_0378_0013, g32p_row02_traceSegment_066_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 405 13 14, g32p_row02_traceSegment_066_0405_0013, g32p_row02_traceSegment_066_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 378 27 27, g32p_row02_traceSegment_066_0378_0027, g32p_row02_traceSegment_066_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 324 54 54, g32p_row02_traceSegment_066_0324_0054, g32p_row02_traceSegment_066_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 216 108 108, g32p_row02_traceSegment_066_0216_0108, g32p_row02_traceSegment_066_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_066 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 0 216 216, g32p_row02_traceSegment_066_0000_0216, g32p_row02_traceSegment_066_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 432 13 14, g32p_row02_traceSegment_066_0432_0013, g32p_row02_traceSegment_066_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 459 13 14, g32p_row02_traceSegment_066_0459_0013, g32p_row02_traceSegment_066_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 432 27 27, g32p_row02_traceSegment_066_0432_0027, g32p_row02_traceSegment_066_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 486 13 14, g32p_row02_traceSegment_066_0486_0013, g32p_row02_traceSegment_066_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 513 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 513 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 513 13 14, g32p_row02_traceSegment_066_0513_0013, g32p_row02_traceSegment_066_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 486 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 486 27 27, g32p_row02_traceSegment_066_0486_0027, g32p_row02_traceSegment_066_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 432 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 432 54 54, g32p_row02_traceSegment_066_0432_0054, g32p_row02_traceSegment_066_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 540 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 540 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 540 13 14, g32p_row02_traceSegment_066_0540_0013, g32p_row02_traceSegment_066_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 567 13 14, g32p_row02_traceSegment_066_0567_0013, g32p_row02_traceSegment_066_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 540 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 540 27 27, g32p_row02_traceSegment_066_0540_0027, g32p_row02_traceSegment_066_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 594 13 14, g32p_row02_traceSegment_066_0594_0013, g32p_row02_traceSegment_066_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 621 13 14, g32p_row02_traceSegment_066_0621_0013, g32p_row02_traceSegment_066_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 594 27 27, g32p_row02_traceSegment_066_0594_0027, g32p_row02_traceSegment_066_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 540 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 540 54 54, g32p_row02_traceSegment_066_0540_0054, g32p_row02_traceSegment_066_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 432 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 432 108 108, g32p_row02_traceSegment_066_0432_0108, g32p_row02_traceSegment_066_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 648 13 14, g32p_row02_traceSegment_066_0648_0013, g32p_row02_traceSegment_066_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 688 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 675 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 675 13 14, g32p_row02_traceSegment_066_0675_0013, g32p_row02_traceSegment_066_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 648 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 648 27 27, g32p_row02_traceSegment_066_0648_0027, g32p_row02_traceSegment_066_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 702 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 715 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 702 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 702 13 14, g32p_row02_traceSegment_066_0702_0013, g32p_row02_traceSegment_066_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 729 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 729 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 729 13 14, g32p_row02_traceSegment_066_0729_0013, g32p_row02_traceSegment_066_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 702 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 702 27 27, g32p_row02_traceSegment_066_0702_0027, g32p_row02_traceSegment_066_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 648 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 648 54 54, g32p_row02_traceSegment_066_0648_0054, g32p_row02_traceSegment_066_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 756 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 756 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 756 13 14, g32p_row02_traceSegment_066_0756_0013, g32p_row02_traceSegment_066_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 796 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 783 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 783 13 14, g32p_row02_traceSegment_066_0783_0013, g32p_row02_traceSegment_066_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 756 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 756 27 27, g32p_row02_traceSegment_066_0756_0027, g32p_row02_traceSegment_066_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 810 13 14, g32p_row02_traceSegment_066_0810_0013, g32p_row02_traceSegment_066_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 837 13 14, g32p_row02_traceSegment_066_0837_0013, g32p_row02_traceSegment_066_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 810 27 27, g32p_row02_traceSegment_066_0810_0027, g32p_row02_traceSegment_066_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 756 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 756 54 54, g32p_row02_traceSegment_066_0756_0054, g32p_row02_traceSegment_066_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 648 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 648 108 108, g32p_row02_traceSegment_066_0648_0108, g32p_row02_traceSegment_066_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_066 432 432 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 432 216 216, g32p_row02_traceSegment_066_0432_0216, g32p_row02_traceSegment_066_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_066 0 864 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 0 432 432, g32p_row02_traceSegment_066_0000_0432, g32p_row02_traceSegment_066_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 864 13 14, g32p_row02_traceSegment_066_0864_0013, g32p_row02_traceSegment_066_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 891 13 14, g32p_row02_traceSegment_066_0891_0013, g32p_row02_traceSegment_066_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 864 27 27, g32p_row02_traceSegment_066_0864_0027, g32p_row02_traceSegment_066_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 918 13 14, g32p_row02_traceSegment_066_0918_0013, g32p_row02_traceSegment_066_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 945 13 14, g32p_row02_traceSegment_066_0945_0013, g32p_row02_traceSegment_066_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 918 27 27, g32p_row02_traceSegment_066_0918_0027, g32p_row02_traceSegment_066_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 864 54 54, g32p_row02_traceSegment_066_0864_0054, g32p_row02_traceSegment_066_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 972 13 14, g32p_row02_traceSegment_066_0972_0013, g32p_row02_traceSegment_066_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 999 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1012 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 999 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 999 13 14, g32p_row02_traceSegment_066_0999_0013, g32p_row02_traceSegment_066_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 972 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 972 27 27, g32p_row02_traceSegment_066_0972_0027, g32p_row02_traceSegment_066_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1026 13 14, g32p_row02_traceSegment_066_1026_0013, g32p_row02_traceSegment_066_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1066 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1053 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1053 13 14, g32p_row02_traceSegment_066_1053_0013, g32p_row02_traceSegment_066_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1026 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1026 27 27, g32p_row02_traceSegment_066_1026_0027, g32p_row02_traceSegment_066_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 972 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 972 54 54, g32p_row02_traceSegment_066_0972_0054, g32p_row02_traceSegment_066_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 864 216 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 864 108 108, g32p_row02_traceSegment_066_0864_0108, g32p_row02_traceSegment_066_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1080 13 14, g32p_row02_traceSegment_066_1080_0013, g32p_row02_traceSegment_066_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1107 13 14, g32p_row02_traceSegment_066_1107_0013, g32p_row02_traceSegment_066_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1080 27 27, g32p_row02_traceSegment_066_1080_0027, g32p_row02_traceSegment_066_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1134 13 14, g32p_row02_traceSegment_066_1134_0013, g32p_row02_traceSegment_066_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1161 13 14, g32p_row02_traceSegment_066_1161_0013, g32p_row02_traceSegment_066_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1134 27 27, g32p_row02_traceSegment_066_1134_0027, g32p_row02_traceSegment_066_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1080 54 54, g32p_row02_traceSegment_066_1080_0054, g32p_row02_traceSegment_066_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1188 13 14, g32p_row02_traceSegment_066_1188_0013, g32p_row02_traceSegment_066_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1215 13 14, g32p_row02_traceSegment_066_1215_0013, g32p_row02_traceSegment_066_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1188 27 27, g32p_row02_traceSegment_066_1188_0027, g32p_row02_traceSegment_066_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1242 13 14, g32p_row02_traceSegment_066_1242_0013, g32p_row02_traceSegment_066_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1269 13 14, g32p_row02_traceSegment_066_1269_0013, g32p_row02_traceSegment_066_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1242 27 27, g32p_row02_traceSegment_066_1242_0027, g32p_row02_traceSegment_066_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1188 54 54, g32p_row02_traceSegment_066_1188_0054, g32p_row02_traceSegment_066_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1080 108 108, g32p_row02_traceSegment_066_1080_0108, g32p_row02_traceSegment_066_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_066 864 432 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 864 216 216, g32p_row02_traceSegment_066_0864_0216, g32p_row02_traceSegment_066_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1309 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1296 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1296 13 14, g32p_row02_traceSegment_066_1296_0013, g32p_row02_traceSegment_066_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1323 13 14, g32p_row02_traceSegment_066_1323_0013, g32p_row02_traceSegment_066_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1296 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1296 27 27, g32p_row02_traceSegment_066_1296_0027, g32p_row02_traceSegment_066_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1350 13 14, g32p_row02_traceSegment_066_1350_0013, g32p_row02_traceSegment_066_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1377 13 14, g32p_row02_traceSegment_066_1377_0013, g32p_row02_traceSegment_066_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1350 27 27, g32p_row02_traceSegment_066_1350_0027, g32p_row02_traceSegment_066_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 1296 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1296 54 54, g32p_row02_traceSegment_066_1296_0054, g32p_row02_traceSegment_066_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1404 13 14, g32p_row02_traceSegment_066_1404_0013, g32p_row02_traceSegment_066_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1431 13 14, g32p_row02_traceSegment_066_1431_0013, g32p_row02_traceSegment_066_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1404 27 27, g32p_row02_traceSegment_066_1404_0027, g32p_row02_traceSegment_066_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1458 13 14, g32p_row02_traceSegment_066_1458_0013, g32p_row02_traceSegment_066_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1485 13 14, g32p_row02_traceSegment_066_1485_0013, g32p_row02_traceSegment_066_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1458 27 27, g32p_row02_traceSegment_066_1458_0027, g32p_row02_traceSegment_066_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1404 54 54, g32p_row02_traceSegment_066_1404_0054, g32p_row02_traceSegment_066_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 1296 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1296 108 108, g32p_row02_traceSegment_066_1296_0108, g32p_row02_traceSegment_066_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1512 13 14, g32p_row02_traceSegment_066_1512_0013, g32p_row02_traceSegment_066_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1539 13 14, g32p_row02_traceSegment_066_1539_0013, g32p_row02_traceSegment_066_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1512 27 27, g32p_row02_traceSegment_066_1512_0027, g32p_row02_traceSegment_066_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1566 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1566 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1566 13 14, g32p_row02_traceSegment_066_1566_0013, g32p_row02_traceSegment_066_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1606 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1593 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1593 13 14, g32p_row02_traceSegment_066_1593_0013, g32p_row02_traceSegment_066_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1566 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1566 27 27, g32p_row02_traceSegment_066_1566_0027, g32p_row02_traceSegment_066_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 1512 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1512 54 54, g32p_row02_traceSegment_066_1512_0054, g32p_row02_traceSegment_066_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1620 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1620 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1620 13 14, g32p_row02_traceSegment_066_1620_0013, g32p_row02_traceSegment_066_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1647 13 14, g32p_row02_traceSegment_066_1647_0013, g32p_row02_traceSegment_066_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1620 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1620 27 27, g32p_row02_traceSegment_066_1620_0027, g32p_row02_traceSegment_066_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1674 13 14, g32p_row02_traceSegment_066_1674_0013, g32p_row02_traceSegment_066_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1701 13 14, g32p_row02_traceSegment_066_1701_0013, g32p_row02_traceSegment_066_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1674 27 27, g32p_row02_traceSegment_066_1674_0027, g32p_row02_traceSegment_066_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 1620 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1620 54 54, g32p_row02_traceSegment_066_1620_0054, g32p_row02_traceSegment_066_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 1512 216 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1512 108 108, g32p_row02_traceSegment_066_1512_0108, g32p_row02_traceSegment_066_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_066 1296 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1296 216 216, g32p_row02_traceSegment_066_1296_0216, g32p_row02_traceSegment_066_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_066 864 864 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 864 432 432, g32p_row02_traceSegment_066_0864_0432, g32p_row02_traceSegment_066_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_066 0 1728 = [0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 0 864 864, g32p_row02_traceSegment_066_0000_0864, g32p_row02_traceSegment_066_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1728 13 14, g32p_row02_traceSegment_066_1728_0013, g32p_row02_traceSegment_066_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1768 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1755 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1755 13 14, g32p_row02_traceSegment_066_1755_0013, g32p_row02_traceSegment_066_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1728 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1728 27 27, g32p_row02_traceSegment_066_1728_0027, g32p_row02_traceSegment_066_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1782 13 14, g32p_row02_traceSegment_066_1782_0013, g32p_row02_traceSegment_066_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1809 13 14, g32p_row02_traceSegment_066_1809_0013, g32p_row02_traceSegment_066_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1782 27 27, g32p_row02_traceSegment_066_1782_0027, g32p_row02_traceSegment_066_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 1728 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1728 54 54, g32p_row02_traceSegment_066_1728_0054, g32p_row02_traceSegment_066_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1836 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1849 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1836 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1836 13 14, g32p_row02_traceSegment_066_1836_0013, g32p_row02_traceSegment_066_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1876 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1863 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1863 13 14, g32p_row02_traceSegment_066_1863_0013, g32p_row02_traceSegment_066_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1836 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1836 27 27, g32p_row02_traceSegment_066_1836_0027, g32p_row02_traceSegment_066_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1890 13 14, g32p_row02_traceSegment_066_1890_0013, g32p_row02_traceSegment_066_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1917 13 14, g32p_row02_traceSegment_066_1917_0013, g32p_row02_traceSegment_066_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1890 27 27, g32p_row02_traceSegment_066_1890_0027, g32p_row02_traceSegment_066_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 1836 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1836 54 54, g32p_row02_traceSegment_066_1836_0054, g32p_row02_traceSegment_066_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 1728 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1728 108 108, g32p_row02_traceSegment_066_1728_0108, g32p_row02_traceSegment_066_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1944 13 14, g32p_row02_traceSegment_066_1944_0013, g32p_row02_traceSegment_066_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1971 13 14, g32p_row02_traceSegment_066_1971_0013, g32p_row02_traceSegment_066_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1944 27 27, g32p_row02_traceSegment_066_1944_0027, g32p_row02_traceSegment_066_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1998 13 14, g32p_row02_traceSegment_066_1998_0013, g32p_row02_traceSegment_066_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2025 13 14, g32p_row02_traceSegment_066_2025_0013, g32p_row02_traceSegment_066_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1998 27 27, g32p_row02_traceSegment_066_1998_0027, g32p_row02_traceSegment_066_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1944 54 54, g32p_row02_traceSegment_066_1944_0054, g32p_row02_traceSegment_066_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2052 13 14, g32p_row02_traceSegment_066_2052_0013, g32p_row02_traceSegment_066_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2079 13 14, g32p_row02_traceSegment_066_2079_0013, g32p_row02_traceSegment_066_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2052 27 27, g32p_row02_traceSegment_066_2052_0027, g32p_row02_traceSegment_066_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2106 13 14, g32p_row02_traceSegment_066_2106_0013, g32p_row02_traceSegment_066_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2133 13 14, g32p_row02_traceSegment_066_2133_0013, g32p_row02_traceSegment_066_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2106 27 27, g32p_row02_traceSegment_066_2106_0027, g32p_row02_traceSegment_066_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2052 54 54, g32p_row02_traceSegment_066_2052_0054, g32p_row02_traceSegment_066_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1944 108 108, g32p_row02_traceSegment_066_1944_0108, g32p_row02_traceSegment_066_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_066 1728 432 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1728 216 216, g32p_row02_traceSegment_066_1728_0216, g32p_row02_traceSegment_066_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2173 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2160 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2160 13 14, g32p_row02_traceSegment_066_2160_0013, g32p_row02_traceSegment_066_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2187 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2187 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2187 13 14, g32p_row02_traceSegment_066_2187_0013, g32p_row02_traceSegment_066_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2160 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2160 27 27, g32p_row02_traceSegment_066_2160_0027, g32p_row02_traceSegment_066_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2214 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2214 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2214 13 14, g32p_row02_traceSegment_066_2214_0013, g32p_row02_traceSegment_066_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2241 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2241 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2241 13 14, g32p_row02_traceSegment_066_2241_0013, g32p_row02_traceSegment_066_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2214 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2214 27 27, g32p_row02_traceSegment_066_2214_0027, g32p_row02_traceSegment_066_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 2160 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2160 54 54, g32p_row02_traceSegment_066_2160_0054, g32p_row02_traceSegment_066_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2268 13 14, g32p_row02_traceSegment_066_2268_0013, g32p_row02_traceSegment_066_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2295 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2295 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2295 13 14, g32p_row02_traceSegment_066_2295_0013, g32p_row02_traceSegment_066_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2268 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2268 27 27, g32p_row02_traceSegment_066_2268_0027, g32p_row02_traceSegment_066_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2322 13 14, g32p_row02_traceSegment_066_2322_0013, g32p_row02_traceSegment_066_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2349 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2349 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2349 13 14, g32p_row02_traceSegment_066_2349_0013, g32p_row02_traceSegment_066_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2322 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2322 27 27, g32p_row02_traceSegment_066_2322_0027, g32p_row02_traceSegment_066_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 2268 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2268 54 54, g32p_row02_traceSegment_066_2268_0054, g32p_row02_traceSegment_066_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 2160 216 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2160 108 108, g32p_row02_traceSegment_066_2160_0108, g32p_row02_traceSegment_066_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2376 13 14, g32p_row02_traceSegment_066_2376_0013, g32p_row02_traceSegment_066_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2403 13 14, g32p_row02_traceSegment_066_2403_0013, g32p_row02_traceSegment_066_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2376 27 27, g32p_row02_traceSegment_066_2376_0027, g32p_row02_traceSegment_066_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2430 13 14, g32p_row02_traceSegment_066_2430_0013, g32p_row02_traceSegment_066_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2457 13 14, g32p_row02_traceSegment_066_2457_0013, g32p_row02_traceSegment_066_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2430 27 27, g32p_row02_traceSegment_066_2430_0027, g32p_row02_traceSegment_066_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2376 54 54, g32p_row02_traceSegment_066_2376_0054, g32p_row02_traceSegment_066_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2484 13 14, g32p_row02_traceSegment_066_2484_0013, g32p_row02_traceSegment_066_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2511 13 14, g32p_row02_traceSegment_066_2511_0013, g32p_row02_traceSegment_066_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2484 27 27, g32p_row02_traceSegment_066_2484_0027, g32p_row02_traceSegment_066_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2538 13 14, g32p_row02_traceSegment_066_2538_0013, g32p_row02_traceSegment_066_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2565 13 14, g32p_row02_traceSegment_066_2565_0013, g32p_row02_traceSegment_066_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2538 27 27, g32p_row02_traceSegment_066_2538_0027, g32p_row02_traceSegment_066_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2484 54 54, g32p_row02_traceSegment_066_2484_0054, g32p_row02_traceSegment_066_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2376 108 108, g32p_row02_traceSegment_066_2376_0108, g32p_row02_traceSegment_066_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_066 2160 432 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2160 216 216, g32p_row02_traceSegment_066_2160_0216, g32p_row02_traceSegment_066_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_066 1728 864 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1728 432 432, g32p_row02_traceSegment_066_1728_0432, g32p_row02_traceSegment_066_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2592 13 14, g32p_row02_traceSegment_066_2592_0013, g32p_row02_traceSegment_066_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2619 13 14, g32p_row02_traceSegment_066_2619_0013, g32p_row02_traceSegment_066_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2592 27 27, g32p_row02_traceSegment_066_2592_0027, g32p_row02_traceSegment_066_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2646 13 14, g32p_row02_traceSegment_066_2646_0013, g32p_row02_traceSegment_066_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2673 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2673 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2673 13 14, g32p_row02_traceSegment_066_2673_0013, g32p_row02_traceSegment_066_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2646 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2646 27 27, g32p_row02_traceSegment_066_2646_0027, g32p_row02_traceSegment_066_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 2592 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2592 54 54, g32p_row02_traceSegment_066_2592_0054, g32p_row02_traceSegment_066_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2700 13 14, g32p_row02_traceSegment_066_2700_0013, g32p_row02_traceSegment_066_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2740 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2727 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2727 13 14, g32p_row02_traceSegment_066_2727_0013, g32p_row02_traceSegment_066_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2700 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2700 27 27, g32p_row02_traceSegment_066_2700_0027, g32p_row02_traceSegment_066_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2754 13 14, g32p_row02_traceSegment_066_2754_0013, g32p_row02_traceSegment_066_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2794 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2781 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2781 13 14, g32p_row02_traceSegment_066_2781_0013, g32p_row02_traceSegment_066_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2754 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2754 27 27, g32p_row02_traceSegment_066_2754_0027, g32p_row02_traceSegment_066_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 2700 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2700 54 54, g32p_row02_traceSegment_066_2700_0054, g32p_row02_traceSegment_066_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 2592 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2592 108 108, g32p_row02_traceSegment_066_2592_0108, g32p_row02_traceSegment_066_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2808 13 14, g32p_row02_traceSegment_066_2808_0013, g32p_row02_traceSegment_066_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2835 13 14, g32p_row02_traceSegment_066_2835_0013, g32p_row02_traceSegment_066_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2808 27 27, g32p_row02_traceSegment_066_2808_0027, g32p_row02_traceSegment_066_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2862 13 14, g32p_row02_traceSegment_066_2862_0013, g32p_row02_traceSegment_066_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2889 13 14, g32p_row02_traceSegment_066_2889_0013, g32p_row02_traceSegment_066_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2862 27 27, g32p_row02_traceSegment_066_2862_0027, g32p_row02_traceSegment_066_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2808 54 54, g32p_row02_traceSegment_066_2808_0054, g32p_row02_traceSegment_066_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2916 13 14, g32p_row02_traceSegment_066_2916_0013, g32p_row02_traceSegment_066_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2943 13 14, g32p_row02_traceSegment_066_2943_0013, g32p_row02_traceSegment_066_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2916 27 27, g32p_row02_traceSegment_066_2916_0027, g32p_row02_traceSegment_066_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2970 13 14, g32p_row02_traceSegment_066_2970_0013, g32p_row02_traceSegment_066_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2997 13 14, g32p_row02_traceSegment_066_2997_0013, g32p_row02_traceSegment_066_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2970 27 27, g32p_row02_traceSegment_066_2970_0027, g32p_row02_traceSegment_066_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2916 54 54, g32p_row02_traceSegment_066_2916_0054, g32p_row02_traceSegment_066_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2808 108 108, g32p_row02_traceSegment_066_2808_0108, g32p_row02_traceSegment_066_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_066 2592 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2592 216 216, g32p_row02_traceSegment_066_2592_0216, g32p_row02_traceSegment_066_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3024 13 14, g32p_row02_traceSegment_066_3024_0013, g32p_row02_traceSegment_066_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3051 13 14, g32p_row02_traceSegment_066_3051_0013, g32p_row02_traceSegment_066_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3024 27 27, g32p_row02_traceSegment_066_3024_0027, g32p_row02_traceSegment_066_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3078 13 14, g32p_row02_traceSegment_066_3078_0013, g32p_row02_traceSegment_066_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3105 13 14, g32p_row02_traceSegment_066_3105_0013, g32p_row02_traceSegment_066_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3078 27 27, g32p_row02_traceSegment_066_3078_0027, g32p_row02_traceSegment_066_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3024 54 54, g32p_row02_traceSegment_066_3024_0054, g32p_row02_traceSegment_066_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3132 13 14, g32p_row02_traceSegment_066_3132_0013, g32p_row02_traceSegment_066_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3159 13 14, g32p_row02_traceSegment_066_3159_0013, g32p_row02_traceSegment_066_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3132 27 27, g32p_row02_traceSegment_066_3132_0027, g32p_row02_traceSegment_066_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3186 13 14, g32p_row02_traceSegment_066_3186_0013, g32p_row02_traceSegment_066_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3213 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3213 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3213 13 14, g32p_row02_traceSegment_066_3213_0013, g32p_row02_traceSegment_066_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 3186 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3186 27 27, g32p_row02_traceSegment_066_3186_0027, g32p_row02_traceSegment_066_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 3132 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3132 54 54, g32p_row02_traceSegment_066_3132_0054, g32p_row02_traceSegment_066_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 3024 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3024 108 108, g32p_row02_traceSegment_066_3024_0108, g32p_row02_traceSegment_066_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3240 13 14, g32p_row02_traceSegment_066_3240_0013, g32p_row02_traceSegment_066_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3267 13 14, g32p_row02_traceSegment_066_3267_0013, g32p_row02_traceSegment_066_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3240 27 27, g32p_row02_traceSegment_066_3240_0027, g32p_row02_traceSegment_066_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3294 13 14, g32p_row02_traceSegment_066_3294_0013, g32p_row02_traceSegment_066_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3321 13 14, g32p_row02_traceSegment_066_3321_0013, g32p_row02_traceSegment_066_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3294 27 27, g32p_row02_traceSegment_066_3294_0027, g32p_row02_traceSegment_066_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3240 54 54, g32p_row02_traceSegment_066_3240_0054, g32p_row02_traceSegment_066_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3348 13 14, g32p_row02_traceSegment_066_3348_0013, g32p_row02_traceSegment_066_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3375 13 14, g32p_row02_traceSegment_066_3375_0013, g32p_row02_traceSegment_066_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3348 27 27, g32p_row02_traceSegment_066_3348_0027, g32p_row02_traceSegment_066_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3402 13 14, g32p_row02_traceSegment_066_3402_0013, g32p_row02_traceSegment_066_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_066 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_066 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_066_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_066 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3429 13 14, g32p_row02_traceSegment_066_3429_0013, g32p_row02_traceSegment_066_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_066 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3402 27 27, g32p_row02_traceSegment_066_3402_0027, g32p_row02_traceSegment_066_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_066 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3348 54 54, g32p_row02_traceSegment_066_3348_0054, g32p_row02_traceSegment_066_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_066 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3240 108 108, g32p_row02_traceSegment_066_3240_0108, g32p_row02_traceSegment_066_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_066_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_066 3024 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 3024 216 216, g32p_row02_traceSegment_066_3024_0216, g32p_row02_traceSegment_066_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_066_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_066 2592 864 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 2592 432 432, g32p_row02_traceSegment_066_2592_0432, g32p_row02_traceSegment_066_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_066_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_066 1728 1728 = [0, 0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 1728 864 864, g32p_row02_traceSegment_066_1728_0864, g32p_row02_traceSegment_066_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_066_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_066 0 3456 = [0, 0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_066 0 1728 1728, g32p_row02_traceSegment_066_0000_1728, g32p_row02_traceSegment_066_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 66 = [0, 0, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_066_0000_3456

end HodgeLean.Foundations.Program

end
end
