import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_020 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 20 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_020_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 0 13 14, g32p_row02_traceSegment_020_0000_0013, g32p_row02_traceSegment_020_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 27 13 14, g32p_row02_traceSegment_020_0027_0013, g32p_row02_traceSegment_020_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 0 27 27, g32p_row02_traceSegment_020_0000_0027, g32p_row02_traceSegment_020_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 54 13 14, g32p_row02_traceSegment_020_0054_0013, g32p_row02_traceSegment_020_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 81 13 14, g32p_row02_traceSegment_020_0081_0013, g32p_row02_traceSegment_020_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 54 27 27, g32p_row02_traceSegment_020_0054_0027, g32p_row02_traceSegment_020_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 0 54 54, g32p_row02_traceSegment_020_0000_0054, g32p_row02_traceSegment_020_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 108 13 14, g32p_row02_traceSegment_020_0108_0013, g32p_row02_traceSegment_020_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 135 13 14, g32p_row02_traceSegment_020_0135_0013, g32p_row02_traceSegment_020_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 108 27 27, g32p_row02_traceSegment_020_0108_0027, g32p_row02_traceSegment_020_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 162 13 14, g32p_row02_traceSegment_020_0162_0013, g32p_row02_traceSegment_020_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 189 13 14, g32p_row02_traceSegment_020_0189_0013, g32p_row02_traceSegment_020_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 162 27 27, g32p_row02_traceSegment_020_0162_0027, g32p_row02_traceSegment_020_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 108 54 54, g32p_row02_traceSegment_020_0108_0054, g32p_row02_traceSegment_020_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 0 108 108, g32p_row02_traceSegment_020_0000_0108, g32p_row02_traceSegment_020_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 229 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 216 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 216 13 14, g32p_row02_traceSegment_020_0216_0013, g32p_row02_traceSegment_020_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 243 13 14, g32p_row02_traceSegment_020_0243_0013, g32p_row02_traceSegment_020_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 216 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 216 27 27, g32p_row02_traceSegment_020_0216_0027, g32p_row02_traceSegment_020_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 270 13 14, g32p_row02_traceSegment_020_0270_0013, g32p_row02_traceSegment_020_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 297 13 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 310 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 297 27 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 297 13 14, g32p_row02_traceSegment_020_0297_0013, g32p_row02_traceSegment_020_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 270 54 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 270 27 27, g32p_row02_traceSegment_020_0270_0027, g32p_row02_traceSegment_020_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 216 108 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 216 54 54, g32p_row02_traceSegment_020_0216_0054, g32p_row02_traceSegment_020_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 324 13 14, g32p_row02_traceSegment_020_0324_0013, g32p_row02_traceSegment_020_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 351 13 14, g32p_row02_traceSegment_020_0351_0013, g32p_row02_traceSegment_020_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 324 27 27, g32p_row02_traceSegment_020_0324_0027, g32p_row02_traceSegment_020_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 378 13 14, g32p_row02_traceSegment_020_0378_0013, g32p_row02_traceSegment_020_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 405 13 14, g32p_row02_traceSegment_020_0405_0013, g32p_row02_traceSegment_020_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 378 27 27, g32p_row02_traceSegment_020_0378_0027, g32p_row02_traceSegment_020_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 324 54 54, g32p_row02_traceSegment_020_0324_0054, g32p_row02_traceSegment_020_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 216 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 216 108 108, g32p_row02_traceSegment_020_0216_0108, g32p_row02_traceSegment_020_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_020 0 432 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 0 216 216, g32p_row02_traceSegment_020_0000_0216, g32p_row02_traceSegment_020_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 432 13 14, g32p_row02_traceSegment_020_0432_0013, g32p_row02_traceSegment_020_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 459 13 14, g32p_row02_traceSegment_020_0459_0013, g32p_row02_traceSegment_020_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 432 27 27, g32p_row02_traceSegment_020_0432_0027, g32p_row02_traceSegment_020_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 499 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 486 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 486 13 14, g32p_row02_traceSegment_020_0486_0013, g32p_row02_traceSegment_020_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 513 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 513 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 513 13 14, g32p_row02_traceSegment_020_0513_0013, g32p_row02_traceSegment_020_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 486 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 486 27 27, g32p_row02_traceSegment_020_0486_0027, g32p_row02_traceSegment_020_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 432 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 432 54 54, g32p_row02_traceSegment_020_0432_0054, g32p_row02_traceSegment_020_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 540 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 540 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 540 13 14, g32p_row02_traceSegment_020_0540_0013, g32p_row02_traceSegment_020_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 580 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 567 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 567 13 14, g32p_row02_traceSegment_020_0567_0013, g32p_row02_traceSegment_020_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 540 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 540 27 27, g32p_row02_traceSegment_020_0540_0027, g32p_row02_traceSegment_020_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 594 13 14, g32p_row02_traceSegment_020_0594_0013, g32p_row02_traceSegment_020_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 621 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 634 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 621 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 621 13 14, g32p_row02_traceSegment_020_0621_0013, g32p_row02_traceSegment_020_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 594 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 594 27 27, g32p_row02_traceSegment_020_0594_0027, g32p_row02_traceSegment_020_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 540 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 540 54 54, g32p_row02_traceSegment_020_0540_0054, g32p_row02_traceSegment_020_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 432 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 432 108 108, g32p_row02_traceSegment_020_0432_0108, g32p_row02_traceSegment_020_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 661 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 648 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 648 13 14, g32p_row02_traceSegment_020_0648_0013, g32p_row02_traceSegment_020_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 675 13 14, g32p_row02_traceSegment_020_0675_0013, g32p_row02_traceSegment_020_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 648 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 648 27 27, g32p_row02_traceSegment_020_0648_0027, g32p_row02_traceSegment_020_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 715 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 702 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 702 13 14, g32p_row02_traceSegment_020_0702_0013, g32p_row02_traceSegment_020_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 729 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 729 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 729 13 14, g32p_row02_traceSegment_020_0729_0013, g32p_row02_traceSegment_020_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 702 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 702 27 27, g32p_row02_traceSegment_020_0702_0027, g32p_row02_traceSegment_020_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 648 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 648 54 54, g32p_row02_traceSegment_020_0648_0054, g32p_row02_traceSegment_020_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 756 13 14, g32p_row02_traceSegment_020_0756_0013, g32p_row02_traceSegment_020_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 796 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 783 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 783 13 14, g32p_row02_traceSegment_020_0783_0013, g32p_row02_traceSegment_020_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 756 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 756 27 27, g32p_row02_traceSegment_020_0756_0027, g32p_row02_traceSegment_020_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 823 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 810 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 810 13 14, g32p_row02_traceSegment_020_0810_0013, g32p_row02_traceSegment_020_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 837 13 14, g32p_row02_traceSegment_020_0837_0013, g32p_row02_traceSegment_020_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 810 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 810 27 27, g32p_row02_traceSegment_020_0810_0027, g32p_row02_traceSegment_020_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 756 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 756 54 54, g32p_row02_traceSegment_020_0756_0054, g32p_row02_traceSegment_020_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 648 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 648 108 108, g32p_row02_traceSegment_020_0648_0108, g32p_row02_traceSegment_020_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_020 432 432 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 432 216 216, g32p_row02_traceSegment_020_0432_0216, g32p_row02_traceSegment_020_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_020 0 864 = [0, 0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 0 432 432, g32p_row02_traceSegment_020_0000_0432, g32p_row02_traceSegment_020_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 864 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 864 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 864 13 14, g32p_row02_traceSegment_020_0864_0013, g32p_row02_traceSegment_020_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 904 14 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 891 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 891 13 14, g32p_row02_traceSegment_020_0891_0013, g32p_row02_traceSegment_020_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 864 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 864 27 27, g32p_row02_traceSegment_020_0864_0027, g32p_row02_traceSegment_020_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 918 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 918 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 918 13 14, g32p_row02_traceSegment_020_0918_0013, g32p_row02_traceSegment_020_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 945 13 14, g32p_row02_traceSegment_020_0945_0013, g32p_row02_traceSegment_020_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 918 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 918 27 27, g32p_row02_traceSegment_020_0918_0027, g32p_row02_traceSegment_020_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 864 108 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 864 54 54, g32p_row02_traceSegment_020_0864_0054, g32p_row02_traceSegment_020_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 972 13 14, g32p_row02_traceSegment_020_0972_0013, g32p_row02_traceSegment_020_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1012 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 999 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 999 13 14, g32p_row02_traceSegment_020_0999_0013, g32p_row02_traceSegment_020_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 972 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 972 27 27, g32p_row02_traceSegment_020_0972_0027, g32p_row02_traceSegment_020_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1039 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1026 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1026 13 14, g32p_row02_traceSegment_020_1026_0013, g32p_row02_traceSegment_020_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1066 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1053 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1053 13 14, g32p_row02_traceSegment_020_1053_0013, g32p_row02_traceSegment_020_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1026 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1026 27 27, g32p_row02_traceSegment_020_1026_0027, g32p_row02_traceSegment_020_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 972 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 972 54 54, g32p_row02_traceSegment_020_0972_0054, g32p_row02_traceSegment_020_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 864 216 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 864 108 108, g32p_row02_traceSegment_020_0864_0108, g32p_row02_traceSegment_020_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1080 13 14, g32p_row02_traceSegment_020_1080_0013, g32p_row02_traceSegment_020_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1107 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1107 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1107 13 14, g32p_row02_traceSegment_020_1107_0013, g32p_row02_traceSegment_020_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1080 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1080 27 27, g32p_row02_traceSegment_020_1080_0027, g32p_row02_traceSegment_020_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1134 13 14, g32p_row02_traceSegment_020_1134_0013, g32p_row02_traceSegment_020_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1161 13 14, g32p_row02_traceSegment_020_1161_0013, g32p_row02_traceSegment_020_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1134 27 27, g32p_row02_traceSegment_020_1134_0027, g32p_row02_traceSegment_020_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 1080 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1080 54 54, g32p_row02_traceSegment_020_1080_0054, g32p_row02_traceSegment_020_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1188 13 14, g32p_row02_traceSegment_020_1188_0013, g32p_row02_traceSegment_020_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1215 13 14, g32p_row02_traceSegment_020_1215_0013, g32p_row02_traceSegment_020_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1188 27 27, g32p_row02_traceSegment_020_1188_0027, g32p_row02_traceSegment_020_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1242 13 14, g32p_row02_traceSegment_020_1242_0013, g32p_row02_traceSegment_020_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1269 13 14, g32p_row02_traceSegment_020_1269_0013, g32p_row02_traceSegment_020_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1242 27 27, g32p_row02_traceSegment_020_1242_0027, g32p_row02_traceSegment_020_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1188 54 54, g32p_row02_traceSegment_020_1188_0054, g32p_row02_traceSegment_020_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 1080 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1080 108 108, g32p_row02_traceSegment_020_1080_0108, g32p_row02_traceSegment_020_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_020 864 432 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 864 216 216, g32p_row02_traceSegment_020_0864_0216, g32p_row02_traceSegment_020_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1296 13 14, g32p_row02_traceSegment_020_1296_0013, g32p_row02_traceSegment_020_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1323 13 14, g32p_row02_traceSegment_020_1323_0013, g32p_row02_traceSegment_020_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1296 27 27, g32p_row02_traceSegment_020_1296_0027, g32p_row02_traceSegment_020_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1350 13 14, g32p_row02_traceSegment_020_1350_0013, g32p_row02_traceSegment_020_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1377 13 14, g32p_row02_traceSegment_020_1377_0013, g32p_row02_traceSegment_020_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1350 27 27, g32p_row02_traceSegment_020_1350_0027, g32p_row02_traceSegment_020_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1296 54 54, g32p_row02_traceSegment_020_1296_0054, g32p_row02_traceSegment_020_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1404 13 14, g32p_row02_traceSegment_020_1404_0013, g32p_row02_traceSegment_020_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1431 13 14, g32p_row02_traceSegment_020_1431_0013, g32p_row02_traceSegment_020_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1404 27 27, g32p_row02_traceSegment_020_1404_0027, g32p_row02_traceSegment_020_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1458 13 14, g32p_row02_traceSegment_020_1458_0013, g32p_row02_traceSegment_020_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1485 13 14, g32p_row02_traceSegment_020_1485_0013, g32p_row02_traceSegment_020_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1458 27 27, g32p_row02_traceSegment_020_1458_0027, g32p_row02_traceSegment_020_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1404 54 54, g32p_row02_traceSegment_020_1404_0054, g32p_row02_traceSegment_020_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1296 108 108, g32p_row02_traceSegment_020_1296_0108, g32p_row02_traceSegment_020_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1512 13 14, g32p_row02_traceSegment_020_1512_0013, g32p_row02_traceSegment_020_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1552 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1539 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1539 13 14, g32p_row02_traceSegment_020_1539_0013, g32p_row02_traceSegment_020_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1512 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1512 27 27, g32p_row02_traceSegment_020_1512_0027, g32p_row02_traceSegment_020_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1566 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1579 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1566 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1566 13 14, g32p_row02_traceSegment_020_1566_0013, g32p_row02_traceSegment_020_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1593 13 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1606 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1593 27 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1593 13 14, g32p_row02_traceSegment_020_1593_0013, g32p_row02_traceSegment_020_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1566 54 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1566 27 27, g32p_row02_traceSegment_020_1566_0027, g32p_row02_traceSegment_020_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 1512 108 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1512 54 54, g32p_row02_traceSegment_020_1512_0054, g32p_row02_traceSegment_020_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1620 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1633 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1620 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1620 13 14, g32p_row02_traceSegment_020_1620_0013, g32p_row02_traceSegment_020_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1647 13 14, g32p_row02_traceSegment_020_1647_0013, g32p_row02_traceSegment_020_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1620 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1620 27 27, g32p_row02_traceSegment_020_1620_0027, g32p_row02_traceSegment_020_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1674 13 14, g32p_row02_traceSegment_020_1674_0013, g32p_row02_traceSegment_020_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1701 13 14, g32p_row02_traceSegment_020_1701_0013, g32p_row02_traceSegment_020_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1674 27 27, g32p_row02_traceSegment_020_1674_0027, g32p_row02_traceSegment_020_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 1620 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1620 54 54, g32p_row02_traceSegment_020_1620_0054, g32p_row02_traceSegment_020_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 1512 216 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1512 108 108, g32p_row02_traceSegment_020_1512_0108, g32p_row02_traceSegment_020_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_020 1296 432 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1296 216 216, g32p_row02_traceSegment_020_1296_0216, g32p_row02_traceSegment_020_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_020 864 864 = [0, 0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 864 432 432, g32p_row02_traceSegment_020_0864_0432, g32p_row02_traceSegment_020_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_020 0 1728 = [0, 0, 0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 0 864 864, g32p_row02_traceSegment_020_0000_0864, g32p_row02_traceSegment_020_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1728 13 14, g32p_row02_traceSegment_020_1728_0013, g32p_row02_traceSegment_020_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1755 13 14, g32p_row02_traceSegment_020_1755_0013, g32p_row02_traceSegment_020_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1728 27 27, g32p_row02_traceSegment_020_1728_0027, g32p_row02_traceSegment_020_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1782 13 14, g32p_row02_traceSegment_020_1782_0013, g32p_row02_traceSegment_020_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1809 13 14, g32p_row02_traceSegment_020_1809_0013, g32p_row02_traceSegment_020_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1782 27 27, g32p_row02_traceSegment_020_1782_0027, g32p_row02_traceSegment_020_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1728 54 54, g32p_row02_traceSegment_020_1728_0054, g32p_row02_traceSegment_020_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1836 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1836 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1836 13 14, g32p_row02_traceSegment_020_1836_0013, g32p_row02_traceSegment_020_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1863 13 14, g32p_row02_traceSegment_020_1863_0013, g32p_row02_traceSegment_020_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1836 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1836 27 27, g32p_row02_traceSegment_020_1836_0027, g32p_row02_traceSegment_020_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1890 13 14, g32p_row02_traceSegment_020_1890_0013, g32p_row02_traceSegment_020_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1917 13 14, g32p_row02_traceSegment_020_1917_0013, g32p_row02_traceSegment_020_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1890 27 27, g32p_row02_traceSegment_020_1890_0027, g32p_row02_traceSegment_020_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 1836 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1836 54 54, g32p_row02_traceSegment_020_1836_0054, g32p_row02_traceSegment_020_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 1728 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1728 108 108, g32p_row02_traceSegment_020_1728_0108, g32p_row02_traceSegment_020_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1944 13 14, g32p_row02_traceSegment_020_1944_0013, g32p_row02_traceSegment_020_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1971 13 14, g32p_row02_traceSegment_020_1971_0013, g32p_row02_traceSegment_020_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1944 27 27, g32p_row02_traceSegment_020_1944_0027, g32p_row02_traceSegment_020_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1998 13 14, g32p_row02_traceSegment_020_1998_0013, g32p_row02_traceSegment_020_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2025 13 14, g32p_row02_traceSegment_020_2025_0013, g32p_row02_traceSegment_020_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1998 27 27, g32p_row02_traceSegment_020_1998_0027, g32p_row02_traceSegment_020_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1944 54 54, g32p_row02_traceSegment_020_1944_0054, g32p_row02_traceSegment_020_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2052 13 14, g32p_row02_traceSegment_020_2052_0013, g32p_row02_traceSegment_020_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2079 13 14, g32p_row02_traceSegment_020_2079_0013, g32p_row02_traceSegment_020_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2052 27 27, g32p_row02_traceSegment_020_2052_0027, g32p_row02_traceSegment_020_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2106 13 14, g32p_row02_traceSegment_020_2106_0013, g32p_row02_traceSegment_020_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2133 13 14, g32p_row02_traceSegment_020_2133_0013, g32p_row02_traceSegment_020_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2106 27 27, g32p_row02_traceSegment_020_2106_0027, g32p_row02_traceSegment_020_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2052 54 54, g32p_row02_traceSegment_020_2052_0054, g32p_row02_traceSegment_020_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1944 108 108, g32p_row02_traceSegment_020_1944_0108, g32p_row02_traceSegment_020_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_020 1728 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1728 216 216, g32p_row02_traceSegment_020_1728_0216, g32p_row02_traceSegment_020_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2160 13 14, g32p_row02_traceSegment_020_2160_0013, g32p_row02_traceSegment_020_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2187 13 14, g32p_row02_traceSegment_020_2187_0013, g32p_row02_traceSegment_020_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2160 27 27, g32p_row02_traceSegment_020_2160_0027, g32p_row02_traceSegment_020_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2214 13 14, g32p_row02_traceSegment_020_2214_0013, g32p_row02_traceSegment_020_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2241 13 14, g32p_row02_traceSegment_020_2241_0013, g32p_row02_traceSegment_020_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2214 27 27, g32p_row02_traceSegment_020_2214_0027, g32p_row02_traceSegment_020_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2160 54 54, g32p_row02_traceSegment_020_2160_0054, g32p_row02_traceSegment_020_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2268 13 14, g32p_row02_traceSegment_020_2268_0013, g32p_row02_traceSegment_020_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2295 13 14, g32p_row02_traceSegment_020_2295_0013, g32p_row02_traceSegment_020_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2268 27 27, g32p_row02_traceSegment_020_2268_0027, g32p_row02_traceSegment_020_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2322 13 14, g32p_row02_traceSegment_020_2322_0013, g32p_row02_traceSegment_020_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2349 13 14, g32p_row02_traceSegment_020_2349_0013, g32p_row02_traceSegment_020_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2322 27 27, g32p_row02_traceSegment_020_2322_0027, g32p_row02_traceSegment_020_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2268 54 54, g32p_row02_traceSegment_020_2268_0054, g32p_row02_traceSegment_020_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2160 108 108, g32p_row02_traceSegment_020_2160_0108, g32p_row02_traceSegment_020_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2376 13 14, g32p_row02_traceSegment_020_2376_0013, g32p_row02_traceSegment_020_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2403 13 14, g32p_row02_traceSegment_020_2403_0013, g32p_row02_traceSegment_020_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2376 27 27, g32p_row02_traceSegment_020_2376_0027, g32p_row02_traceSegment_020_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2430 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2443 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2430 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2430 13 14, g32p_row02_traceSegment_020_2430_0013, g32p_row02_traceSegment_020_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2457 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2457 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2457 13 14, g32p_row02_traceSegment_020_2457_0013, g32p_row02_traceSegment_020_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2430 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2430 27 27, g32p_row02_traceSegment_020_2430_0027, g32p_row02_traceSegment_020_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 2376 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2376 54 54, g32p_row02_traceSegment_020_2376_0054, g32p_row02_traceSegment_020_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2484 13 14, g32p_row02_traceSegment_020_2484_0013, g32p_row02_traceSegment_020_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2511 13 14, g32p_row02_traceSegment_020_2511_0013, g32p_row02_traceSegment_020_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2484 27 27, g32p_row02_traceSegment_020_2484_0027, g32p_row02_traceSegment_020_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2538 13 14, g32p_row02_traceSegment_020_2538_0013, g32p_row02_traceSegment_020_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2565 13 14, g32p_row02_traceSegment_020_2565_0013, g32p_row02_traceSegment_020_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2538 27 27, g32p_row02_traceSegment_020_2538_0027, g32p_row02_traceSegment_020_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2484 54 54, g32p_row02_traceSegment_020_2484_0054, g32p_row02_traceSegment_020_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 2376 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2376 108 108, g32p_row02_traceSegment_020_2376_0108, g32p_row02_traceSegment_020_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_020 2160 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2160 216 216, g32p_row02_traceSegment_020_2160_0216, g32p_row02_traceSegment_020_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_020 1728 864 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1728 432 432, g32p_row02_traceSegment_020_1728_0432, g32p_row02_traceSegment_020_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2592 13 14, g32p_row02_traceSegment_020_2592_0013, g32p_row02_traceSegment_020_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2619 13 14, g32p_row02_traceSegment_020_2619_0013, g32p_row02_traceSegment_020_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2592 27 27, g32p_row02_traceSegment_020_2592_0027, g32p_row02_traceSegment_020_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2646 13 14, g32p_row02_traceSegment_020_2646_0013, g32p_row02_traceSegment_020_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2673 13 14, g32p_row02_traceSegment_020_2673_0013, g32p_row02_traceSegment_020_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2646 27 27, g32p_row02_traceSegment_020_2646_0027, g32p_row02_traceSegment_020_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2592 54 54, g32p_row02_traceSegment_020_2592_0054, g32p_row02_traceSegment_020_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2700 13 14, g32p_row02_traceSegment_020_2700_0013, g32p_row02_traceSegment_020_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2740 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2727 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2727 13 14, g32p_row02_traceSegment_020_2727_0013, g32p_row02_traceSegment_020_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2700 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2700 27 27, g32p_row02_traceSegment_020_2700_0027, g32p_row02_traceSegment_020_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2754 13 14, g32p_row02_traceSegment_020_2754_0013, g32p_row02_traceSegment_020_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2781 13 14, g32p_row02_traceSegment_020_2781_0013, g32p_row02_traceSegment_020_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2754 27 27, g32p_row02_traceSegment_020_2754_0027, g32p_row02_traceSegment_020_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 2700 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2700 54 54, g32p_row02_traceSegment_020_2700_0054, g32p_row02_traceSegment_020_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 2592 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2592 108 108, g32p_row02_traceSegment_020_2592_0108, g32p_row02_traceSegment_020_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2808 13 14, g32p_row02_traceSegment_020_2808_0013, g32p_row02_traceSegment_020_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2835 13 14, g32p_row02_traceSegment_020_2835_0013, g32p_row02_traceSegment_020_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2808 27 27, g32p_row02_traceSegment_020_2808_0027, g32p_row02_traceSegment_020_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2862 13 14, g32p_row02_traceSegment_020_2862_0013, g32p_row02_traceSegment_020_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2889 13 14, g32p_row02_traceSegment_020_2889_0013, g32p_row02_traceSegment_020_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2862 27 27, g32p_row02_traceSegment_020_2862_0027, g32p_row02_traceSegment_020_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2808 54 54, g32p_row02_traceSegment_020_2808_0054, g32p_row02_traceSegment_020_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2916 13 14, g32p_row02_traceSegment_020_2916_0013, g32p_row02_traceSegment_020_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2943 13 14, g32p_row02_traceSegment_020_2943_0013, g32p_row02_traceSegment_020_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2916 27 27, g32p_row02_traceSegment_020_2916_0027, g32p_row02_traceSegment_020_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2970 13 14, g32p_row02_traceSegment_020_2970_0013, g32p_row02_traceSegment_020_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2997 13 14, g32p_row02_traceSegment_020_2997_0013, g32p_row02_traceSegment_020_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2970 27 27, g32p_row02_traceSegment_020_2970_0027, g32p_row02_traceSegment_020_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2916 54 54, g32p_row02_traceSegment_020_2916_0054, g32p_row02_traceSegment_020_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2808 108 108, g32p_row02_traceSegment_020_2808_0108, g32p_row02_traceSegment_020_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_020 2592 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2592 216 216, g32p_row02_traceSegment_020_2592_0216, g32p_row02_traceSegment_020_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3024 13 14, g32p_row02_traceSegment_020_3024_0013, g32p_row02_traceSegment_020_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3051 13 14, g32p_row02_traceSegment_020_3051_0013, g32p_row02_traceSegment_020_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3024 27 27, g32p_row02_traceSegment_020_3024_0027, g32p_row02_traceSegment_020_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3078 13 14, g32p_row02_traceSegment_020_3078_0013, g32p_row02_traceSegment_020_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3105 13 14, g32p_row02_traceSegment_020_3105_0013, g32p_row02_traceSegment_020_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3078 27 27, g32p_row02_traceSegment_020_3078_0027, g32p_row02_traceSegment_020_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3024 54 54, g32p_row02_traceSegment_020_3024_0054, g32p_row02_traceSegment_020_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3132 13 14, g32p_row02_traceSegment_020_3132_0013, g32p_row02_traceSegment_020_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3159 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3159 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3159 13 14, g32p_row02_traceSegment_020_3159_0013, g32p_row02_traceSegment_020_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 3132 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3132 27 27, g32p_row02_traceSegment_020_3132_0027, g32p_row02_traceSegment_020_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3186 13 14, g32p_row02_traceSegment_020_3186_0013, g32p_row02_traceSegment_020_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3213 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3213 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3213 13 14, g32p_row02_traceSegment_020_3213_0013, g32p_row02_traceSegment_020_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 3186 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3186 27 27, g32p_row02_traceSegment_020_3186_0027, g32p_row02_traceSegment_020_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 3132 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3132 54 54, g32p_row02_traceSegment_020_3132_0054, g32p_row02_traceSegment_020_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 3024 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3024 108 108, g32p_row02_traceSegment_020_3024_0108, g32p_row02_traceSegment_020_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3240 13 14, g32p_row02_traceSegment_020_3240_0013, g32p_row02_traceSegment_020_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3267 13 14, g32p_row02_traceSegment_020_3267_0013, g32p_row02_traceSegment_020_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3240 27 27, g32p_row02_traceSegment_020_3240_0027, g32p_row02_traceSegment_020_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3294 13 14, g32p_row02_traceSegment_020_3294_0013, g32p_row02_traceSegment_020_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3321 13 14, g32p_row02_traceSegment_020_3321_0013, g32p_row02_traceSegment_020_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3294 27 27, g32p_row02_traceSegment_020_3294_0027, g32p_row02_traceSegment_020_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3240 54 54, g32p_row02_traceSegment_020_3240_0054, g32p_row02_traceSegment_020_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3348 13 14, g32p_row02_traceSegment_020_3348_0013, g32p_row02_traceSegment_020_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3375 13 14, g32p_row02_traceSegment_020_3375_0013, g32p_row02_traceSegment_020_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3348 27 27, g32p_row02_traceSegment_020_3348_0027, g32p_row02_traceSegment_020_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3402 13 14, g32p_row02_traceSegment_020_3402_0013, g32p_row02_traceSegment_020_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_020 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_020 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_020_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_020 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3429 13 14, g32p_row02_traceSegment_020_3429_0013, g32p_row02_traceSegment_020_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_020 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3402 27 27, g32p_row02_traceSegment_020_3402_0027, g32p_row02_traceSegment_020_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_020 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3348 54 54, g32p_row02_traceSegment_020_3348_0054, g32p_row02_traceSegment_020_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_020 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3240 108 108, g32p_row02_traceSegment_020_3240_0108, g32p_row02_traceSegment_020_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_020_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_020 3024 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 3024 216 216, g32p_row02_traceSegment_020_3024_0216, g32p_row02_traceSegment_020_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_020_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_020 2592 864 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 2592 432 432, g32p_row02_traceSegment_020_2592_0432, g32p_row02_traceSegment_020_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_020_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_020 1728 1728 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 1728 864 864, g32p_row02_traceSegment_020_1728_0864, g32p_row02_traceSegment_020_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_020_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_020 0 3456 = [0, 0, 0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_020 0 1728 1728, g32p_row02_traceSegment_020_0000_1728, g32p_row02_traceSegment_020_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 20 = [0, 0, 0, 0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_020_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_021 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 21 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_021_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 0 13 14, g32p_row02_traceSegment_021_0000_0013, g32p_row02_traceSegment_021_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 27 13 14, g32p_row02_traceSegment_021_0027_0013, g32p_row02_traceSegment_021_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 0 27 27, g32p_row02_traceSegment_021_0000_0027, g32p_row02_traceSegment_021_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 54 13 14, g32p_row02_traceSegment_021_0054_0013, g32p_row02_traceSegment_021_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 94 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 81 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 81 13 14, g32p_row02_traceSegment_021_0081_0013, g32p_row02_traceSegment_021_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 54 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 54 27 27, g32p_row02_traceSegment_021_0054_0027, g32p_row02_traceSegment_021_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 0 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 0 54 54, g32p_row02_traceSegment_021_0000_0054, g32p_row02_traceSegment_021_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 121 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 108 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 108 13 14, g32p_row02_traceSegment_021_0108_0013, g32p_row02_traceSegment_021_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 135 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 135 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 135 13 14, g32p_row02_traceSegment_021_0135_0013, g32p_row02_traceSegment_021_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 108 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 108 27 27, g32p_row02_traceSegment_021_0108_0027, g32p_row02_traceSegment_021_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 162 13 14, g32p_row02_traceSegment_021_0162_0013, g32p_row02_traceSegment_021_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 189 13 14, g32p_row02_traceSegment_021_0189_0013, g32p_row02_traceSegment_021_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 162 27 27, g32p_row02_traceSegment_021_0162_0027, g32p_row02_traceSegment_021_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 108 108 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 108 54 54, g32p_row02_traceSegment_021_0108_0054, g32p_row02_traceSegment_021_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 0 216 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 0 108 108, g32p_row02_traceSegment_021_0000_0108, g32p_row02_traceSegment_021_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 216 13 14, g32p_row02_traceSegment_021_0216_0013, g32p_row02_traceSegment_021_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 243 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 256 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 243 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 243 13 14, g32p_row02_traceSegment_021_0243_0013, g32p_row02_traceSegment_021_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 216 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 216 27 27, g32p_row02_traceSegment_021_0216_0027, g32p_row02_traceSegment_021_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 270 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 270 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 270 13 14, g32p_row02_traceSegment_021_0270_0013, g32p_row02_traceSegment_021_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 297 13 14, g32p_row02_traceSegment_021_0297_0013, g32p_row02_traceSegment_021_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 270 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 270 27 27, g32p_row02_traceSegment_021_0270_0027, g32p_row02_traceSegment_021_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 216 108 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 216 54 54, g32p_row02_traceSegment_021_0216_0054, g32p_row02_traceSegment_021_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 337 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 324 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 324 13 14, g32p_row02_traceSegment_021_0324_0013, g32p_row02_traceSegment_021_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 351 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 351 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 351 13 14, g32p_row02_traceSegment_021_0351_0013, g32p_row02_traceSegment_021_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 324 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 324 27 27, g32p_row02_traceSegment_021_0324_0027, g32p_row02_traceSegment_021_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 378 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 391 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 378 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 378 13 14, g32p_row02_traceSegment_021_0378_0013, g32p_row02_traceSegment_021_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 418 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 405 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 405 13 14, g32p_row02_traceSegment_021_0405_0013, g32p_row02_traceSegment_021_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 378 54 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 378 27 27, g32p_row02_traceSegment_021_0378_0027, g32p_row02_traceSegment_021_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 324 108 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 324 54 54, g32p_row02_traceSegment_021_0324_0054, g32p_row02_traceSegment_021_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 216 216 = [0, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 216 108 108, g32p_row02_traceSegment_021_0216_0108, g32p_row02_traceSegment_021_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_021 0 432 = [0, 0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 0 216 216, g32p_row02_traceSegment_021_0000_0216, g32p_row02_traceSegment_021_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 432 13 14, g32p_row02_traceSegment_021_0432_0013, g32p_row02_traceSegment_021_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 459 13 14, g32p_row02_traceSegment_021_0459_0013, g32p_row02_traceSegment_021_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 432 27 27, g32p_row02_traceSegment_021_0432_0027, g32p_row02_traceSegment_021_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 486 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 486 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 486 13 14, g32p_row02_traceSegment_021_0486_0013, g32p_row02_traceSegment_021_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 513 13 14, g32p_row02_traceSegment_021_0513_0013, g32p_row02_traceSegment_021_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 486 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 486 27 27, g32p_row02_traceSegment_021_0486_0027, g32p_row02_traceSegment_021_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 432 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 432 54 54, g32p_row02_traceSegment_021_0432_0054, g32p_row02_traceSegment_021_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 540 13 14, g32p_row02_traceSegment_021_0540_0013, g32p_row02_traceSegment_021_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 567 13 14, g32p_row02_traceSegment_021_0567_0013, g32p_row02_traceSegment_021_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 540 27 27, g32p_row02_traceSegment_021_0540_0027, g32p_row02_traceSegment_021_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 594 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 607 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 594 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 594 13 14, g32p_row02_traceSegment_021_0594_0013, g32p_row02_traceSegment_021_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 621 13 14, g32p_row02_traceSegment_021_0621_0013, g32p_row02_traceSegment_021_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 594 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 594 27 27, g32p_row02_traceSegment_021_0594_0027, g32p_row02_traceSegment_021_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 540 108 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 540 54 54, g32p_row02_traceSegment_021_0540_0054, g32p_row02_traceSegment_021_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 432 216 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 432 108 108, g32p_row02_traceSegment_021_0432_0108, g32p_row02_traceSegment_021_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 648 13 14, g32p_row02_traceSegment_021_0648_0013, g32p_row02_traceSegment_021_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 675 13 14, g32p_row02_traceSegment_021_0675_0013, g32p_row02_traceSegment_021_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 648 27 27, g32p_row02_traceSegment_021_0648_0027, g32p_row02_traceSegment_021_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 702 13 14, g32p_row02_traceSegment_021_0702_0013, g32p_row02_traceSegment_021_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 742 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 729 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 729 13 14, g32p_row02_traceSegment_021_0729_0013, g32p_row02_traceSegment_021_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 702 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 702 27 27, g32p_row02_traceSegment_021_0702_0027, g32p_row02_traceSegment_021_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 648 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 648 54 54, g32p_row02_traceSegment_021_0648_0054, g32p_row02_traceSegment_021_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 756 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 769 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 756 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 756 13 14, g32p_row02_traceSegment_021_0756_0013, g32p_row02_traceSegment_021_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 783 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 783 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 783 13 14, g32p_row02_traceSegment_021_0783_0013, g32p_row02_traceSegment_021_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 756 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 756 27 27, g32p_row02_traceSegment_021_0756_0027, g32p_row02_traceSegment_021_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 810 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 810 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 810 13 14, g32p_row02_traceSegment_021_0810_0013, g32p_row02_traceSegment_021_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 837 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 837 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 837 13 14, g32p_row02_traceSegment_021_0837_0013, g32p_row02_traceSegment_021_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 810 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 810 27 27, g32p_row02_traceSegment_021_0810_0027, g32p_row02_traceSegment_021_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 756 108 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 756 54 54, g32p_row02_traceSegment_021_0756_0054, g32p_row02_traceSegment_021_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 648 216 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 648 108 108, g32p_row02_traceSegment_021_0648_0108, g32p_row02_traceSegment_021_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_021 432 432 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 432 216 216, g32p_row02_traceSegment_021_0432_0216, g32p_row02_traceSegment_021_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_021 0 864 = [0, 12, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 0 432 432, g32p_row02_traceSegment_021_0000_0432, g32p_row02_traceSegment_021_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 864 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 864 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 864 13 14, g32p_row02_traceSegment_021_0864_0013, g32p_row02_traceSegment_021_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 891 13 14, g32p_row02_traceSegment_021_0891_0013, g32p_row02_traceSegment_021_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 864 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 864 27 27, g32p_row02_traceSegment_021_0864_0027, g32p_row02_traceSegment_021_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 918 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 918 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 918 13 14, g32p_row02_traceSegment_021_0918_0013, g32p_row02_traceSegment_021_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 958 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 945 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 945 13 14, g32p_row02_traceSegment_021_0945_0013, g32p_row02_traceSegment_021_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 918 54 = [0, 4, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 918 27 27, g32p_row02_traceSegment_021_0918_0027, g32p_row02_traceSegment_021_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 864 108 = [0, 4, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 864 54 54, g32p_row02_traceSegment_021_0864_0054, g32p_row02_traceSegment_021_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 972 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 985 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 972 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 972 13 14, g32p_row02_traceSegment_021_0972_0013, g32p_row02_traceSegment_021_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 999 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 999 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 999 13 14, g32p_row02_traceSegment_021_0999_0013, g32p_row02_traceSegment_021_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 972 54 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 972 27 27, g32p_row02_traceSegment_021_0972_0027, g32p_row02_traceSegment_021_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1026 13 14, g32p_row02_traceSegment_021_1026_0013, g32p_row02_traceSegment_021_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1053 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1066 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1053 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1053 13 14, g32p_row02_traceSegment_021_1053_0013, g32p_row02_traceSegment_021_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1026 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1026 27 27, g32p_row02_traceSegment_021_1026_0027, g32p_row02_traceSegment_021_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 972 108 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 972 54 54, g32p_row02_traceSegment_021_0972_0054, g32p_row02_traceSegment_021_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 864 216 = [0, 13, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 864 108 108, g32p_row02_traceSegment_021_0864_0108, g32p_row02_traceSegment_021_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1080 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1093 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1080 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1080 13 14, g32p_row02_traceSegment_021_1080_0013, g32p_row02_traceSegment_021_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1120 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1107 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1107 13 14, g32p_row02_traceSegment_021_1107_0013, g32p_row02_traceSegment_021_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1080 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1080 27 27, g32p_row02_traceSegment_021_1080_0027, g32p_row02_traceSegment_021_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1134 13 14, g32p_row02_traceSegment_021_1134_0013, g32p_row02_traceSegment_021_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1174 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1161 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1161 13 14, g32p_row02_traceSegment_021_1161_0013, g32p_row02_traceSegment_021_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1134 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1134 27 27, g32p_row02_traceSegment_021_1134_0027, g32p_row02_traceSegment_021_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 1080 108 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1080 54 54, g32p_row02_traceSegment_021_1080_0054, g32p_row02_traceSegment_021_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1188 13 = [0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1201 14 = [0, 1, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1188 27 = [0, 6, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1188 13 14, g32p_row02_traceSegment_021_1188_0013, g32p_row02_traceSegment_021_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1215 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1228 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1215 27 = [0, 3, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1215 13 14, g32p_row02_traceSegment_021_1215_0013, g32p_row02_traceSegment_021_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1188 54 = [0, 9, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1188 27 27, g32p_row02_traceSegment_021_1188_0027, g32p_row02_traceSegment_021_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1242 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1255 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1242 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1242 13 14, g32p_row02_traceSegment_021_1242_0013, g32p_row02_traceSegment_021_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1269 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1282 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1269 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1269 13 14, g32p_row02_traceSegment_021_1269_0013, g32p_row02_traceSegment_021_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1242 54 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1242 27 27, g32p_row02_traceSegment_021_1242_0027, g32p_row02_traceSegment_021_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 1188 108 = [0, 17, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1188 54 54, g32p_row02_traceSegment_021_1188_0054, g32p_row02_traceSegment_021_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 1080 216 = [0, 24, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1080 108 108, g32p_row02_traceSegment_021_1080_0108, g32p_row02_traceSegment_021_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_021 864 432 = [0, 37, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 864 216 216, g32p_row02_traceSegment_021_0864_0216, g32p_row02_traceSegment_021_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1296 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1296 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1296 13 14, g32p_row02_traceSegment_021_1296_0013, g32p_row02_traceSegment_021_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1323 13 = [0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1323 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1323 13 14, g32p_row02_traceSegment_021_1323_0013, g32p_row02_traceSegment_021_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1296 54 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1296 27 27, g32p_row02_traceSegment_021_1296_0027, g32p_row02_traceSegment_021_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1350 13 14, g32p_row02_traceSegment_021_1350_0013, g32p_row02_traceSegment_021_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1377 13 14, g32p_row02_traceSegment_021_1377_0013, g32p_row02_traceSegment_021_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1350 27 27, g32p_row02_traceSegment_021_1350_0027, g32p_row02_traceSegment_021_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 1296 108 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1296 54 54, g32p_row02_traceSegment_021_1296_0054, g32p_row02_traceSegment_021_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1404 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1417 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1404 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1404 13 14, g32p_row02_traceSegment_021_1404_0013, g32p_row02_traceSegment_021_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1431 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1444 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1431 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1431 13 14, g32p_row02_traceSegment_021_1431_0013, g32p_row02_traceSegment_021_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1404 54 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1404 27 27, g32p_row02_traceSegment_021_1404_0027, g32p_row02_traceSegment_021_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1458 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1471 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1458 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1458 13 14, g32p_row02_traceSegment_021_1458_0013, g32p_row02_traceSegment_021_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1485 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1498 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1485 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1485 13 14, g32p_row02_traceSegment_021_1485_0013, g32p_row02_traceSegment_021_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1458 54 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1458 27 27, g32p_row02_traceSegment_021_1458_0027, g32p_row02_traceSegment_021_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 1404 108 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1404 54 54, g32p_row02_traceSegment_021_1404_0054, g32p_row02_traceSegment_021_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 1296 216 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1296 108 108, g32p_row02_traceSegment_021_1296_0108, g32p_row02_traceSegment_021_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1512 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1525 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1512 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1512 13 14, g32p_row02_traceSegment_021_1512_0013, g32p_row02_traceSegment_021_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1539 13 14, g32p_row02_traceSegment_021_1539_0013, g32p_row02_traceSegment_021_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1512 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1512 27 27, g32p_row02_traceSegment_021_1512_0027, g32p_row02_traceSegment_021_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1566 13 14, g32p_row02_traceSegment_021_1566_0013, g32p_row02_traceSegment_021_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1593 13 14, g32p_row02_traceSegment_021_1593_0013, g32p_row02_traceSegment_021_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1566 27 27, g32p_row02_traceSegment_021_1566_0027, g32p_row02_traceSegment_021_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 1512 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1512 54 54, g32p_row02_traceSegment_021_1512_0054, g32p_row02_traceSegment_021_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1633 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1620 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1620 13 14, g32p_row02_traceSegment_021_1620_0013, g32p_row02_traceSegment_021_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1647 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1647 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1647 13 14, g32p_row02_traceSegment_021_1647_0013, g32p_row02_traceSegment_021_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1620 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1620 27 27, g32p_row02_traceSegment_021_1620_0027, g32p_row02_traceSegment_021_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1674 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1687 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1674 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1674 13 14, g32p_row02_traceSegment_021_1674_0013, g32p_row02_traceSegment_021_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1701 13 14, g32p_row02_traceSegment_021_1701_0013, g32p_row02_traceSegment_021_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1674 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1674 27 27, g32p_row02_traceSegment_021_1674_0027, g32p_row02_traceSegment_021_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 1620 108 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1620 54 54, g32p_row02_traceSegment_021_1620_0054, g32p_row02_traceSegment_021_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 1512 216 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1512 108 108, g32p_row02_traceSegment_021_1512_0108, g32p_row02_traceSegment_021_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_021 1296 432 = [0, 30] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1296 216 216, g32p_row02_traceSegment_021_1296_0216, g32p_row02_traceSegment_021_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_021 864 864 = [0, 67, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 864 432 432, g32p_row02_traceSegment_021_0864_0432, g32p_row02_traceSegment_021_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_021 0 1728 = [0, 79, 0, 0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 0 864 864, g32p_row02_traceSegment_021_0000_0864, g32p_row02_traceSegment_021_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1741 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1728 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1728 13 14, g32p_row02_traceSegment_021_1728_0013, g32p_row02_traceSegment_021_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1768 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1755 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1755 13 14, g32p_row02_traceSegment_021_1755_0013, g32p_row02_traceSegment_021_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1728 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1728 27 27, g32p_row02_traceSegment_021_1728_0027, g32p_row02_traceSegment_021_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1782 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1795 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1782 27 = [0, 1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1782 13 14, g32p_row02_traceSegment_021_1782_0013, g32p_row02_traceSegment_021_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1822 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1809 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1809 13 14, g32p_row02_traceSegment_021_1809_0013, g32p_row02_traceSegment_021_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1782 54 = [0, 1, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1782 27 27, g32p_row02_traceSegment_021_1782_0027, g32p_row02_traceSegment_021_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 1728 108 = [0, 4, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1728 54 54, g32p_row02_traceSegment_021_1728_0054, g32p_row02_traceSegment_021_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1836 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1849 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1836 27 = [0, 2, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1836 13 14, g32p_row02_traceSegment_021_1836_0013, g32p_row02_traceSegment_021_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1863 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1876 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1863 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1863 13 14, g32p_row02_traceSegment_021_1863_0013, g32p_row02_traceSegment_021_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1836 54 = [0, 5, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1836 27 27, g32p_row02_traceSegment_021_1836_0027, g32p_row02_traceSegment_021_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1890 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1903 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1890 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1890 13 14, g32p_row02_traceSegment_021_1890_0013, g32p_row02_traceSegment_021_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1917 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1917 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1917 13 14, g32p_row02_traceSegment_021_1917_0013, g32p_row02_traceSegment_021_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1890 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1890 27 27, g32p_row02_traceSegment_021_1890_0027, g32p_row02_traceSegment_021_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 1836 108 = [0, 9, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1836 54 54, g32p_row02_traceSegment_021_1836_0054, g32p_row02_traceSegment_021_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 1728 216 = [0, 13, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1728 108 108, g32p_row02_traceSegment_021_1728_0108, g32p_row02_traceSegment_021_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1944 13 14, g32p_row02_traceSegment_021_1944_0013, g32p_row02_traceSegment_021_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 1984 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1971 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1971 13 14, g32p_row02_traceSegment_021_1971_0013, g32p_row02_traceSegment_021_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1944 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1944 27 27, g32p_row02_traceSegment_021_1944_0027, g32p_row02_traceSegment_021_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1998 13 14, g32p_row02_traceSegment_021_1998_0013, g32p_row02_traceSegment_021_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2025 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2025 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2025 13 14, g32p_row02_traceSegment_021_2025_0013, g32p_row02_traceSegment_021_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 1998 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1998 27 27, g32p_row02_traceSegment_021_1998_0027, g32p_row02_traceSegment_021_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 1944 108 = [0, 1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1944 54 54, g32p_row02_traceSegment_021_1944_0054, g32p_row02_traceSegment_021_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2052 13 14, g32p_row02_traceSegment_021_2052_0013, g32p_row02_traceSegment_021_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2079 13 14, g32p_row02_traceSegment_021_2079_0013, g32p_row02_traceSegment_021_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2052 27 27, g32p_row02_traceSegment_021_2052_0027, g32p_row02_traceSegment_021_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2106 13 14, g32p_row02_traceSegment_021_2106_0013, g32p_row02_traceSegment_021_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2146 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2133 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2133 13 14, g32p_row02_traceSegment_021_2133_0013, g32p_row02_traceSegment_021_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2106 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2106 27 27, g32p_row02_traceSegment_021_2106_0027, g32p_row02_traceSegment_021_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 2052 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2052 54 54, g32p_row02_traceSegment_021_2052_0054, g32p_row02_traceSegment_021_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 1944 216 = [0, 1, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1944 108 108, g32p_row02_traceSegment_021_1944_0108, g32p_row02_traceSegment_021_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_021 1728 432 = [0, 14, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1728 216 216, g32p_row02_traceSegment_021_1728_0216, g32p_row02_traceSegment_021_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2173 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2160 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2160 13 14, g32p_row02_traceSegment_021_2160_0013, g32p_row02_traceSegment_021_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2187 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2200 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2187 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2187 13 14, g32p_row02_traceSegment_021_2187_0013, g32p_row02_traceSegment_021_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2160 54 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2160 27 27, g32p_row02_traceSegment_021_2160_0027, g32p_row02_traceSegment_021_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2227 14 = [0, 1, 0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2214 27 = [0, 1, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2214 13 14, g32p_row02_traceSegment_021_2214_0013, g32p_row02_traceSegment_021_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2241 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2254 14 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2241 27 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2241 13 14, g32p_row02_traceSegment_021_2241_0013, g32p_row02_traceSegment_021_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2214 54 = [0, 1, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2214 27 27, g32p_row02_traceSegment_021_2214_0027, g32p_row02_traceSegment_021_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 2160 108 = [0, 1, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2160 54 54, g32p_row02_traceSegment_021_2160_0054, g32p_row02_traceSegment_021_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2268 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2281 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2268 27 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2268 13 14, g32p_row02_traceSegment_021_2268_0013, g32p_row02_traceSegment_021_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2295 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2295 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2295 13 14, g32p_row02_traceSegment_021_2295_0013, g32p_row02_traceSegment_021_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2268 54 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2268 27 27, g32p_row02_traceSegment_021_2268_0027, g32p_row02_traceSegment_021_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2335 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2322 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2322 13 14, g32p_row02_traceSegment_021_2322_0013, g32p_row02_traceSegment_021_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2349 13 14, g32p_row02_traceSegment_021_2349_0013, g32p_row02_traceSegment_021_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2322 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2322 27 27, g32p_row02_traceSegment_021_2322_0027, g32p_row02_traceSegment_021_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 2268 108 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2268 54 54, g32p_row02_traceSegment_021_2268_0054, g32p_row02_traceSegment_021_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 2160 216 = [0, 1, 0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2160 108 108, g32p_row02_traceSegment_021_2160_0108, g32p_row02_traceSegment_021_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2376 13 14, g32p_row02_traceSegment_021_2376_0013, g32p_row02_traceSegment_021_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2416 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2403 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2403 13 14, g32p_row02_traceSegment_021_2403_0013, g32p_row02_traceSegment_021_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2376 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2376 27 27, g32p_row02_traceSegment_021_2376_0027, g32p_row02_traceSegment_021_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2430 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2430 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2430 13 14, g32p_row02_traceSegment_021_2430_0013, g32p_row02_traceSegment_021_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2457 13 14, g32p_row02_traceSegment_021_2457_0013, g32p_row02_traceSegment_021_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2430 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2430 27 27, g32p_row02_traceSegment_021_2430_0027, g32p_row02_traceSegment_021_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 2376 108 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2376 54 54, g32p_row02_traceSegment_021_2376_0054, g32p_row02_traceSegment_021_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2484 13 14, g32p_row02_traceSegment_021_2484_0013, g32p_row02_traceSegment_021_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2511 13 14, g32p_row02_traceSegment_021_2511_0013, g32p_row02_traceSegment_021_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2484 27 27, g32p_row02_traceSegment_021_2484_0027, g32p_row02_traceSegment_021_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2538 13 14, g32p_row02_traceSegment_021_2538_0013, g32p_row02_traceSegment_021_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2565 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2578 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2565 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2565 13 14, g32p_row02_traceSegment_021_2565_0013, g32p_row02_traceSegment_021_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2538 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2538 27 27, g32p_row02_traceSegment_021_2538_0027, g32p_row02_traceSegment_021_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 2484 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2484 54 54, g32p_row02_traceSegment_021_2484_0054, g32p_row02_traceSegment_021_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 2376 216 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2376 108 108, g32p_row02_traceSegment_021_2376_0108, g32p_row02_traceSegment_021_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_021 2160 432 = [0, 1, 0, 0, 0, 29] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2160 216 216, g32p_row02_traceSegment_021_2160_0216, g32p_row02_traceSegment_021_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_021 1728 864 = [0, 15, 0, 0, 0, 38] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1728 432 432, g32p_row02_traceSegment_021_1728_0432, g32p_row02_traceSegment_021_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2592 13 14, g32p_row02_traceSegment_021_2592_0013, g32p_row02_traceSegment_021_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2619 13 14, g32p_row02_traceSegment_021_2619_0013, g32p_row02_traceSegment_021_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2592 27 27, g32p_row02_traceSegment_021_2592_0027, g32p_row02_traceSegment_021_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2646 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2659 14 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2646 27 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2646 13 14, g32p_row02_traceSegment_021_2646_0013, g32p_row02_traceSegment_021_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2673 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2686 14 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2673 27 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2673 13 14, g32p_row02_traceSegment_021_2673_0013, g32p_row02_traceSegment_021_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2646 54 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2646 27 27, g32p_row02_traceSegment_021_2646_0027, g32p_row02_traceSegment_021_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 2592 108 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2592 54 54, g32p_row02_traceSegment_021_2592_0054, g32p_row02_traceSegment_021_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2700 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2713 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2700 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2700 13 14, g32p_row02_traceSegment_021_2700_0013, g32p_row02_traceSegment_021_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2740 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2727 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2727 13 14, g32p_row02_traceSegment_021_2727_0013, g32p_row02_traceSegment_021_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2700 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2700 27 27, g32p_row02_traceSegment_021_2700_0027, g32p_row02_traceSegment_021_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2754 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2767 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2754 27 = [0, 2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2754 13 14, g32p_row02_traceSegment_021_2754_0013, g32p_row02_traceSegment_021_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2781 13 14, g32p_row02_traceSegment_021_2781_0013, g32p_row02_traceSegment_021_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2754 54 = [0, 2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2754 27 27, g32p_row02_traceSegment_021_2754_0027, g32p_row02_traceSegment_021_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 2700 108 = [0, 2, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2700 54 54, g32p_row02_traceSegment_021_2700_0054, g32p_row02_traceSegment_021_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 2592 216 = [0, 2, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2592 108 108, g32p_row02_traceSegment_021_2592_0108, g32p_row02_traceSegment_021_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2808 13 14, g32p_row02_traceSegment_021_2808_0013, g32p_row02_traceSegment_021_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2835 13 14, g32p_row02_traceSegment_021_2835_0013, g32p_row02_traceSegment_021_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2808 27 27, g32p_row02_traceSegment_021_2808_0027, g32p_row02_traceSegment_021_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2862 13 14, g32p_row02_traceSegment_021_2862_0013, g32p_row02_traceSegment_021_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2889 13 14, g32p_row02_traceSegment_021_2889_0013, g32p_row02_traceSegment_021_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2862 27 27, g32p_row02_traceSegment_021_2862_0027, g32p_row02_traceSegment_021_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2808 54 54, g32p_row02_traceSegment_021_2808_0054, g32p_row02_traceSegment_021_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2916 13 14, g32p_row02_traceSegment_021_2916_0013, g32p_row02_traceSegment_021_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2943 13 14, g32p_row02_traceSegment_021_2943_0013, g32p_row02_traceSegment_021_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2916 27 27, g32p_row02_traceSegment_021_2916_0027, g32p_row02_traceSegment_021_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2970 13 14, g32p_row02_traceSegment_021_2970_0013, g32p_row02_traceSegment_021_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2997 13 14, g32p_row02_traceSegment_021_2997_0013, g32p_row02_traceSegment_021_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2970 27 27, g32p_row02_traceSegment_021_2970_0027, g32p_row02_traceSegment_021_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2916 54 54, g32p_row02_traceSegment_021_2916_0054, g32p_row02_traceSegment_021_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2808 108 108, g32p_row02_traceSegment_021_2808_0108, g32p_row02_traceSegment_021_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_021 2592 432 = [0, 2, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2592 216 216, g32p_row02_traceSegment_021_2592_0216, g32p_row02_traceSegment_021_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3024 13 14, g32p_row02_traceSegment_021_3024_0013, g32p_row02_traceSegment_021_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3051 13 14, g32p_row02_traceSegment_021_3051_0013, g32p_row02_traceSegment_021_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3024 27 27, g32p_row02_traceSegment_021_3024_0027, g32p_row02_traceSegment_021_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3078 13 14, g32p_row02_traceSegment_021_3078_0013, g32p_row02_traceSegment_021_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3105 13 14, g32p_row02_traceSegment_021_3105_0013, g32p_row02_traceSegment_021_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3078 27 27, g32p_row02_traceSegment_021_3078_0027, g32p_row02_traceSegment_021_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3024 54 54, g32p_row02_traceSegment_021_3024_0054, g32p_row02_traceSegment_021_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3132 13 14, g32p_row02_traceSegment_021_3132_0013, g32p_row02_traceSegment_021_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3159 13 14, g32p_row02_traceSegment_021_3159_0013, g32p_row02_traceSegment_021_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3132 27 27, g32p_row02_traceSegment_021_3132_0027, g32p_row02_traceSegment_021_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3186 13 14, g32p_row02_traceSegment_021_3186_0013, g32p_row02_traceSegment_021_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3213 13 14, g32p_row02_traceSegment_021_3213_0013, g32p_row02_traceSegment_021_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3186 27 27, g32p_row02_traceSegment_021_3186_0027, g32p_row02_traceSegment_021_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3132 54 54, g32p_row02_traceSegment_021_3132_0054, g32p_row02_traceSegment_021_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3024 108 108, g32p_row02_traceSegment_021_3024_0108, g32p_row02_traceSegment_021_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3240 13 14, g32p_row02_traceSegment_021_3240_0013, g32p_row02_traceSegment_021_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3267 13 14, g32p_row02_traceSegment_021_3267_0013, g32p_row02_traceSegment_021_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3240 27 27, g32p_row02_traceSegment_021_3240_0027, g32p_row02_traceSegment_021_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3294 13 14, g32p_row02_traceSegment_021_3294_0013, g32p_row02_traceSegment_021_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3321 13 14, g32p_row02_traceSegment_021_3321_0013, g32p_row02_traceSegment_021_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3294 27 27, g32p_row02_traceSegment_021_3294_0027, g32p_row02_traceSegment_021_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3240 54 54, g32p_row02_traceSegment_021_3240_0054, g32p_row02_traceSegment_021_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3348 13 14, g32p_row02_traceSegment_021_3348_0013, g32p_row02_traceSegment_021_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3375 13 14, g32p_row02_traceSegment_021_3375_0013, g32p_row02_traceSegment_021_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3348 27 27, g32p_row02_traceSegment_021_3348_0027, g32p_row02_traceSegment_021_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3402 13 14, g32p_row02_traceSegment_021_3402_0013, g32p_row02_traceSegment_021_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_021 3429 13 = [0, 0, 0, 0, 0, 7] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_021 3442 14 = [0, 0, 0, 0, 0, 13] := by
  decide +kernel

private theorem g32p_row02_traceSegment_021_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_021 3429 27 = [0, 0, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3429 13 14, g32p_row02_traceSegment_021_3429_0013, g32p_row02_traceSegment_021_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_021 3402 54 = [0, 0, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3402 27 27, g32p_row02_traceSegment_021_3402_0027, g32p_row02_traceSegment_021_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_021 3348 108 = [0, 0, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3348 54 54, g32p_row02_traceSegment_021_3348_0054, g32p_row02_traceSegment_021_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_021 3240 216 = [0, 0, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3240 108 108, g32p_row02_traceSegment_021_3240_0108, g32p_row02_traceSegment_021_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_021_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_021 3024 432 = [0, 0, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 3024 216 216, g32p_row02_traceSegment_021_3024_0216, g32p_row02_traceSegment_021_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_021_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_021 2592 864 = [0, 2, 0, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 2592 432 432, g32p_row02_traceSegment_021_2592_0432, g32p_row02_traceSegment_021_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_021_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_021 1728 1728 = [0, 17, 0, 0, 0, 74] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 1728 864 864, g32p_row02_traceSegment_021_1728_0864, g32p_row02_traceSegment_021_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_021_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_021 0 3456 = [0, 96, 0, 0, 0, 96] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_021 0 1728 1728, g32p_row02_traceSegment_021_0000_1728, g32p_row02_traceSegment_021_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_021 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 21 = [0, 96, 0, 0, 0, 96] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_021_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_023 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 23 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_023_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 0 13 14, g32p_row02_traceSegment_023_0000_0013, g32p_row02_traceSegment_023_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 27 13 14, g32p_row02_traceSegment_023_0027_0013, g32p_row02_traceSegment_023_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 0 27 27, g32p_row02_traceSegment_023_0000_0027, g32p_row02_traceSegment_023_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 54 13 14, g32p_row02_traceSegment_023_0054_0013, g32p_row02_traceSegment_023_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 81 13 14, g32p_row02_traceSegment_023_0081_0013, g32p_row02_traceSegment_023_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 54 27 27, g32p_row02_traceSegment_023_0054_0027, g32p_row02_traceSegment_023_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 0 54 54, g32p_row02_traceSegment_023_0000_0054, g32p_row02_traceSegment_023_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 108 13 14, g32p_row02_traceSegment_023_0108_0013, g32p_row02_traceSegment_023_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 135 13 14, g32p_row02_traceSegment_023_0135_0013, g32p_row02_traceSegment_023_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 108 27 27, g32p_row02_traceSegment_023_0108_0027, g32p_row02_traceSegment_023_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 162 13 14, g32p_row02_traceSegment_023_0162_0013, g32p_row02_traceSegment_023_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 189 13 14, g32p_row02_traceSegment_023_0189_0013, g32p_row02_traceSegment_023_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 162 27 27, g32p_row02_traceSegment_023_0162_0027, g32p_row02_traceSegment_023_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 108 54 54, g32p_row02_traceSegment_023_0108_0054, g32p_row02_traceSegment_023_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 0 108 108, g32p_row02_traceSegment_023_0000_0108, g32p_row02_traceSegment_023_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 216 13 14, g32p_row02_traceSegment_023_0216_0013, g32p_row02_traceSegment_023_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 243 13 14, g32p_row02_traceSegment_023_0243_0013, g32p_row02_traceSegment_023_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 216 27 27, g32p_row02_traceSegment_023_0216_0027, g32p_row02_traceSegment_023_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 270 13 14, g32p_row02_traceSegment_023_0270_0013, g32p_row02_traceSegment_023_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 297 13 14, g32p_row02_traceSegment_023_0297_0013, g32p_row02_traceSegment_023_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 270 27 27, g32p_row02_traceSegment_023_0270_0027, g32p_row02_traceSegment_023_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 216 54 54, g32p_row02_traceSegment_023_0216_0054, g32p_row02_traceSegment_023_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 324 13 14, g32p_row02_traceSegment_023_0324_0013, g32p_row02_traceSegment_023_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 351 13 14, g32p_row02_traceSegment_023_0351_0013, g32p_row02_traceSegment_023_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 324 27 27, g32p_row02_traceSegment_023_0324_0027, g32p_row02_traceSegment_023_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 378 13 14, g32p_row02_traceSegment_023_0378_0013, g32p_row02_traceSegment_023_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 405 13 14, g32p_row02_traceSegment_023_0405_0013, g32p_row02_traceSegment_023_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 378 27 27, g32p_row02_traceSegment_023_0378_0027, g32p_row02_traceSegment_023_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 324 54 54, g32p_row02_traceSegment_023_0324_0054, g32p_row02_traceSegment_023_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 216 108 108, g32p_row02_traceSegment_023_0216_0108, g32p_row02_traceSegment_023_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_023 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 0 216 216, g32p_row02_traceSegment_023_0000_0216, g32p_row02_traceSegment_023_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 432 13 14, g32p_row02_traceSegment_023_0432_0013, g32p_row02_traceSegment_023_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 459 13 14, g32p_row02_traceSegment_023_0459_0013, g32p_row02_traceSegment_023_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 432 27 27, g32p_row02_traceSegment_023_0432_0027, g32p_row02_traceSegment_023_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 486 13 14, g32p_row02_traceSegment_023_0486_0013, g32p_row02_traceSegment_023_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 513 13 14, g32p_row02_traceSegment_023_0513_0013, g32p_row02_traceSegment_023_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 486 27 27, g32p_row02_traceSegment_023_0486_0027, g32p_row02_traceSegment_023_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 432 54 54, g32p_row02_traceSegment_023_0432_0054, g32p_row02_traceSegment_023_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 540 13 14, g32p_row02_traceSegment_023_0540_0013, g32p_row02_traceSegment_023_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 567 13 14, g32p_row02_traceSegment_023_0567_0013, g32p_row02_traceSegment_023_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 540 27 27, g32p_row02_traceSegment_023_0540_0027, g32p_row02_traceSegment_023_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 594 13 14, g32p_row02_traceSegment_023_0594_0013, g32p_row02_traceSegment_023_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 621 13 14, g32p_row02_traceSegment_023_0621_0013, g32p_row02_traceSegment_023_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 594 27 27, g32p_row02_traceSegment_023_0594_0027, g32p_row02_traceSegment_023_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 540 54 54, g32p_row02_traceSegment_023_0540_0054, g32p_row02_traceSegment_023_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 432 108 108, g32p_row02_traceSegment_023_0432_0108, g32p_row02_traceSegment_023_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 648 13 14, g32p_row02_traceSegment_023_0648_0013, g32p_row02_traceSegment_023_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 675 13 14, g32p_row02_traceSegment_023_0675_0013, g32p_row02_traceSegment_023_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 648 27 27, g32p_row02_traceSegment_023_0648_0027, g32p_row02_traceSegment_023_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 702 13 14, g32p_row02_traceSegment_023_0702_0013, g32p_row02_traceSegment_023_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 729 13 14, g32p_row02_traceSegment_023_0729_0013, g32p_row02_traceSegment_023_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 702 27 27, g32p_row02_traceSegment_023_0702_0027, g32p_row02_traceSegment_023_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 648 54 54, g32p_row02_traceSegment_023_0648_0054, g32p_row02_traceSegment_023_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 756 13 14, g32p_row02_traceSegment_023_0756_0013, g32p_row02_traceSegment_023_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 783 13 14, g32p_row02_traceSegment_023_0783_0013, g32p_row02_traceSegment_023_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 756 27 27, g32p_row02_traceSegment_023_0756_0027, g32p_row02_traceSegment_023_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 810 13 14, g32p_row02_traceSegment_023_0810_0013, g32p_row02_traceSegment_023_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 837 13 14, g32p_row02_traceSegment_023_0837_0013, g32p_row02_traceSegment_023_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 810 27 27, g32p_row02_traceSegment_023_0810_0027, g32p_row02_traceSegment_023_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 756 54 54, g32p_row02_traceSegment_023_0756_0054, g32p_row02_traceSegment_023_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 648 108 108, g32p_row02_traceSegment_023_0648_0108, g32p_row02_traceSegment_023_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_023 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 432 216 216, g32p_row02_traceSegment_023_0432_0216, g32p_row02_traceSegment_023_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_023 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 0 432 432, g32p_row02_traceSegment_023_0000_0432, g32p_row02_traceSegment_023_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 864 13 14, g32p_row02_traceSegment_023_0864_0013, g32p_row02_traceSegment_023_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 891 13 14, g32p_row02_traceSegment_023_0891_0013, g32p_row02_traceSegment_023_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 864 27 27, g32p_row02_traceSegment_023_0864_0027, g32p_row02_traceSegment_023_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 918 13 14, g32p_row02_traceSegment_023_0918_0013, g32p_row02_traceSegment_023_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 945 13 14, g32p_row02_traceSegment_023_0945_0013, g32p_row02_traceSegment_023_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 918 27 27, g32p_row02_traceSegment_023_0918_0027, g32p_row02_traceSegment_023_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 864 54 54, g32p_row02_traceSegment_023_0864_0054, g32p_row02_traceSegment_023_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 972 13 14, g32p_row02_traceSegment_023_0972_0013, g32p_row02_traceSegment_023_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 999 13 14, g32p_row02_traceSegment_023_0999_0013, g32p_row02_traceSegment_023_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 972 27 27, g32p_row02_traceSegment_023_0972_0027, g32p_row02_traceSegment_023_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1026 13 14, g32p_row02_traceSegment_023_1026_0013, g32p_row02_traceSegment_023_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1053 13 14, g32p_row02_traceSegment_023_1053_0013, g32p_row02_traceSegment_023_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1026 27 27, g32p_row02_traceSegment_023_1026_0027, g32p_row02_traceSegment_023_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 972 54 54, g32p_row02_traceSegment_023_0972_0054, g32p_row02_traceSegment_023_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 864 108 108, g32p_row02_traceSegment_023_0864_0108, g32p_row02_traceSegment_023_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1080 13 14, g32p_row02_traceSegment_023_1080_0013, g32p_row02_traceSegment_023_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1107 13 14, g32p_row02_traceSegment_023_1107_0013, g32p_row02_traceSegment_023_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1080 27 27, g32p_row02_traceSegment_023_1080_0027, g32p_row02_traceSegment_023_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1134 13 14, g32p_row02_traceSegment_023_1134_0013, g32p_row02_traceSegment_023_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1161 13 14, g32p_row02_traceSegment_023_1161_0013, g32p_row02_traceSegment_023_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1134 27 27, g32p_row02_traceSegment_023_1134_0027, g32p_row02_traceSegment_023_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1080 54 54, g32p_row02_traceSegment_023_1080_0054, g32p_row02_traceSegment_023_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1188 13 14, g32p_row02_traceSegment_023_1188_0013, g32p_row02_traceSegment_023_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1215 13 14, g32p_row02_traceSegment_023_1215_0013, g32p_row02_traceSegment_023_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1188 27 27, g32p_row02_traceSegment_023_1188_0027, g32p_row02_traceSegment_023_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1242 13 14, g32p_row02_traceSegment_023_1242_0013, g32p_row02_traceSegment_023_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1269 13 14, g32p_row02_traceSegment_023_1269_0013, g32p_row02_traceSegment_023_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1242 27 27, g32p_row02_traceSegment_023_1242_0027, g32p_row02_traceSegment_023_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1188 54 54, g32p_row02_traceSegment_023_1188_0054, g32p_row02_traceSegment_023_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1080 108 108, g32p_row02_traceSegment_023_1080_0108, g32p_row02_traceSegment_023_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_023 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 864 216 216, g32p_row02_traceSegment_023_0864_0216, g32p_row02_traceSegment_023_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1296 13 14, g32p_row02_traceSegment_023_1296_0013, g32p_row02_traceSegment_023_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1323 13 14, g32p_row02_traceSegment_023_1323_0013, g32p_row02_traceSegment_023_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1296 27 27, g32p_row02_traceSegment_023_1296_0027, g32p_row02_traceSegment_023_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1350 13 14, g32p_row02_traceSegment_023_1350_0013, g32p_row02_traceSegment_023_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1377 13 14, g32p_row02_traceSegment_023_1377_0013, g32p_row02_traceSegment_023_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1350 27 27, g32p_row02_traceSegment_023_1350_0027, g32p_row02_traceSegment_023_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1296 54 54, g32p_row02_traceSegment_023_1296_0054, g32p_row02_traceSegment_023_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1404 13 14, g32p_row02_traceSegment_023_1404_0013, g32p_row02_traceSegment_023_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1431 13 14, g32p_row02_traceSegment_023_1431_0013, g32p_row02_traceSegment_023_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1404 27 27, g32p_row02_traceSegment_023_1404_0027, g32p_row02_traceSegment_023_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1458 13 14, g32p_row02_traceSegment_023_1458_0013, g32p_row02_traceSegment_023_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1485 13 14, g32p_row02_traceSegment_023_1485_0013, g32p_row02_traceSegment_023_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1458 27 27, g32p_row02_traceSegment_023_1458_0027, g32p_row02_traceSegment_023_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1404 54 54, g32p_row02_traceSegment_023_1404_0054, g32p_row02_traceSegment_023_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1296 108 108, g32p_row02_traceSegment_023_1296_0108, g32p_row02_traceSegment_023_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1512 13 14, g32p_row02_traceSegment_023_1512_0013, g32p_row02_traceSegment_023_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1539 13 14, g32p_row02_traceSegment_023_1539_0013, g32p_row02_traceSegment_023_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1512 27 27, g32p_row02_traceSegment_023_1512_0027, g32p_row02_traceSegment_023_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1566 13 14, g32p_row02_traceSegment_023_1566_0013, g32p_row02_traceSegment_023_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1593 13 14, g32p_row02_traceSegment_023_1593_0013, g32p_row02_traceSegment_023_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1566 27 27, g32p_row02_traceSegment_023_1566_0027, g32p_row02_traceSegment_023_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1512 54 54, g32p_row02_traceSegment_023_1512_0054, g32p_row02_traceSegment_023_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1620 13 14, g32p_row02_traceSegment_023_1620_0013, g32p_row02_traceSegment_023_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1647 13 14, g32p_row02_traceSegment_023_1647_0013, g32p_row02_traceSegment_023_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1620 27 27, g32p_row02_traceSegment_023_1620_0027, g32p_row02_traceSegment_023_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1674 13 14, g32p_row02_traceSegment_023_1674_0013, g32p_row02_traceSegment_023_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1701 13 14, g32p_row02_traceSegment_023_1701_0013, g32p_row02_traceSegment_023_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1674 27 27, g32p_row02_traceSegment_023_1674_0027, g32p_row02_traceSegment_023_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1620 54 54, g32p_row02_traceSegment_023_1620_0054, g32p_row02_traceSegment_023_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1512 108 108, g32p_row02_traceSegment_023_1512_0108, g32p_row02_traceSegment_023_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_023 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1296 216 216, g32p_row02_traceSegment_023_1296_0216, g32p_row02_traceSegment_023_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_023 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 864 432 432, g32p_row02_traceSegment_023_0864_0432, g32p_row02_traceSegment_023_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_023 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 0 864 864, g32p_row02_traceSegment_023_0000_0864, g32p_row02_traceSegment_023_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1728 13 14, g32p_row02_traceSegment_023_1728_0013, g32p_row02_traceSegment_023_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1755 13 14, g32p_row02_traceSegment_023_1755_0013, g32p_row02_traceSegment_023_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1728 27 27, g32p_row02_traceSegment_023_1728_0027, g32p_row02_traceSegment_023_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1795 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1782 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1782 13 14, g32p_row02_traceSegment_023_1782_0013, g32p_row02_traceSegment_023_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1809 13 14, g32p_row02_traceSegment_023_1809_0013, g32p_row02_traceSegment_023_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1782 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1782 27 27, g32p_row02_traceSegment_023_1782_0027, g32p_row02_traceSegment_023_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 1728 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1728 54 54, g32p_row02_traceSegment_023_1728_0054, g32p_row02_traceSegment_023_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1836 13 14, g32p_row02_traceSegment_023_1836_0013, g32p_row02_traceSegment_023_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1863 13 14, g32p_row02_traceSegment_023_1863_0013, g32p_row02_traceSegment_023_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1836 27 27, g32p_row02_traceSegment_023_1836_0027, g32p_row02_traceSegment_023_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1890 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1890 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1890 13 14, g32p_row02_traceSegment_023_1890_0013, g32p_row02_traceSegment_023_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1917 13 14, g32p_row02_traceSegment_023_1917_0013, g32p_row02_traceSegment_023_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1890 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1890 27 27, g32p_row02_traceSegment_023_1890_0027, g32p_row02_traceSegment_023_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 1836 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1836 54 54, g32p_row02_traceSegment_023_1836_0054, g32p_row02_traceSegment_023_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 1728 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1728 108 108, g32p_row02_traceSegment_023_1728_0108, g32p_row02_traceSegment_023_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1944 13 14, g32p_row02_traceSegment_023_1944_0013, g32p_row02_traceSegment_023_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1971 13 14, g32p_row02_traceSegment_023_1971_0013, g32p_row02_traceSegment_023_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1944 27 27, g32p_row02_traceSegment_023_1944_0027, g32p_row02_traceSegment_023_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1998 13 14, g32p_row02_traceSegment_023_1998_0013, g32p_row02_traceSegment_023_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2025 13 14, g32p_row02_traceSegment_023_2025_0013, g32p_row02_traceSegment_023_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1998 27 27, g32p_row02_traceSegment_023_1998_0027, g32p_row02_traceSegment_023_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1944 54 54, g32p_row02_traceSegment_023_1944_0054, g32p_row02_traceSegment_023_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2052 13 14, g32p_row02_traceSegment_023_2052_0013, g32p_row02_traceSegment_023_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2079 13 14, g32p_row02_traceSegment_023_2079_0013, g32p_row02_traceSegment_023_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2052 27 27, g32p_row02_traceSegment_023_2052_0027, g32p_row02_traceSegment_023_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2106 13 14, g32p_row02_traceSegment_023_2106_0013, g32p_row02_traceSegment_023_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2133 13 14, g32p_row02_traceSegment_023_2133_0013, g32p_row02_traceSegment_023_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2106 27 27, g32p_row02_traceSegment_023_2106_0027, g32p_row02_traceSegment_023_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2052 54 54, g32p_row02_traceSegment_023_2052_0054, g32p_row02_traceSegment_023_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1944 108 108, g32p_row02_traceSegment_023_1944_0108, g32p_row02_traceSegment_023_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_023 1728 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1728 216 216, g32p_row02_traceSegment_023_1728_0216, g32p_row02_traceSegment_023_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2173 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2160 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2160 13 14, g32p_row02_traceSegment_023_2160_0013, g32p_row02_traceSegment_023_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2187 13 14, g32p_row02_traceSegment_023_2187_0013, g32p_row02_traceSegment_023_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2160 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2160 27 27, g32p_row02_traceSegment_023_2160_0027, g32p_row02_traceSegment_023_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2214 13 14, g32p_row02_traceSegment_023_2214_0013, g32p_row02_traceSegment_023_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2241 13 14, g32p_row02_traceSegment_023_2241_0013, g32p_row02_traceSegment_023_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2214 27 27, g32p_row02_traceSegment_023_2214_0027, g32p_row02_traceSegment_023_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 2160 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2160 54 54, g32p_row02_traceSegment_023_2160_0054, g32p_row02_traceSegment_023_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2268 13 14, g32p_row02_traceSegment_023_2268_0013, g32p_row02_traceSegment_023_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2295 13 14, g32p_row02_traceSegment_023_2295_0013, g32p_row02_traceSegment_023_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2268 27 27, g32p_row02_traceSegment_023_2268_0027, g32p_row02_traceSegment_023_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2322 13 14, g32p_row02_traceSegment_023_2322_0013, g32p_row02_traceSegment_023_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2349 13 14, g32p_row02_traceSegment_023_2349_0013, g32p_row02_traceSegment_023_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2322 27 27, g32p_row02_traceSegment_023_2322_0027, g32p_row02_traceSegment_023_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2268 54 54, g32p_row02_traceSegment_023_2268_0054, g32p_row02_traceSegment_023_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 2160 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2160 108 108, g32p_row02_traceSegment_023_2160_0108, g32p_row02_traceSegment_023_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2376 13 14, g32p_row02_traceSegment_023_2376_0013, g32p_row02_traceSegment_023_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2403 13 14, g32p_row02_traceSegment_023_2403_0013, g32p_row02_traceSegment_023_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2376 27 27, g32p_row02_traceSegment_023_2376_0027, g32p_row02_traceSegment_023_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2430 13 14, g32p_row02_traceSegment_023_2430_0013, g32p_row02_traceSegment_023_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2457 13 14, g32p_row02_traceSegment_023_2457_0013, g32p_row02_traceSegment_023_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2430 27 27, g32p_row02_traceSegment_023_2430_0027, g32p_row02_traceSegment_023_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2376 54 54, g32p_row02_traceSegment_023_2376_0054, g32p_row02_traceSegment_023_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2484 13 14, g32p_row02_traceSegment_023_2484_0013, g32p_row02_traceSegment_023_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2511 13 14, g32p_row02_traceSegment_023_2511_0013, g32p_row02_traceSegment_023_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2484 27 27, g32p_row02_traceSegment_023_2484_0027, g32p_row02_traceSegment_023_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2538 13 14, g32p_row02_traceSegment_023_2538_0013, g32p_row02_traceSegment_023_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2565 13 14, g32p_row02_traceSegment_023_2565_0013, g32p_row02_traceSegment_023_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2538 27 27, g32p_row02_traceSegment_023_2538_0027, g32p_row02_traceSegment_023_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2484 54 54, g32p_row02_traceSegment_023_2484_0054, g32p_row02_traceSegment_023_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2376 108 108, g32p_row02_traceSegment_023_2376_0108, g32p_row02_traceSegment_023_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_023 2160 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2160 216 216, g32p_row02_traceSegment_023_2160_0216, g32p_row02_traceSegment_023_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_023 1728 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1728 432 432, g32p_row02_traceSegment_023_1728_0432, g32p_row02_traceSegment_023_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2592 13 14, g32p_row02_traceSegment_023_2592_0013, g32p_row02_traceSegment_023_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2619 13 14, g32p_row02_traceSegment_023_2619_0013, g32p_row02_traceSegment_023_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2592 27 27, g32p_row02_traceSegment_023_2592_0027, g32p_row02_traceSegment_023_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2646 13 14, g32p_row02_traceSegment_023_2646_0013, g32p_row02_traceSegment_023_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2673 13 14, g32p_row02_traceSegment_023_2673_0013, g32p_row02_traceSegment_023_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2646 27 27, g32p_row02_traceSegment_023_2646_0027, g32p_row02_traceSegment_023_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2592 54 54, g32p_row02_traceSegment_023_2592_0054, g32p_row02_traceSegment_023_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2700 13 14, g32p_row02_traceSegment_023_2700_0013, g32p_row02_traceSegment_023_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2727 13 14, g32p_row02_traceSegment_023_2727_0013, g32p_row02_traceSegment_023_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2700 27 27, g32p_row02_traceSegment_023_2700_0027, g32p_row02_traceSegment_023_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2754 13 14, g32p_row02_traceSegment_023_2754_0013, g32p_row02_traceSegment_023_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2781 13 14, g32p_row02_traceSegment_023_2781_0013, g32p_row02_traceSegment_023_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2754 27 27, g32p_row02_traceSegment_023_2754_0027, g32p_row02_traceSegment_023_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2700 54 54, g32p_row02_traceSegment_023_2700_0054, g32p_row02_traceSegment_023_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2592 108 108, g32p_row02_traceSegment_023_2592_0108, g32p_row02_traceSegment_023_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2808 13 14, g32p_row02_traceSegment_023_2808_0013, g32p_row02_traceSegment_023_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2835 13 14, g32p_row02_traceSegment_023_2835_0013, g32p_row02_traceSegment_023_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2808 27 27, g32p_row02_traceSegment_023_2808_0027, g32p_row02_traceSegment_023_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2862 13 14, g32p_row02_traceSegment_023_2862_0013, g32p_row02_traceSegment_023_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2889 13 14, g32p_row02_traceSegment_023_2889_0013, g32p_row02_traceSegment_023_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2862 27 27, g32p_row02_traceSegment_023_2862_0027, g32p_row02_traceSegment_023_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2808 54 54, g32p_row02_traceSegment_023_2808_0054, g32p_row02_traceSegment_023_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2916 13 14, g32p_row02_traceSegment_023_2916_0013, g32p_row02_traceSegment_023_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2943 13 14, g32p_row02_traceSegment_023_2943_0013, g32p_row02_traceSegment_023_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2916 27 27, g32p_row02_traceSegment_023_2916_0027, g32p_row02_traceSegment_023_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2970 13 14, g32p_row02_traceSegment_023_2970_0013, g32p_row02_traceSegment_023_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2997 13 14, g32p_row02_traceSegment_023_2997_0013, g32p_row02_traceSegment_023_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2970 27 27, g32p_row02_traceSegment_023_2970_0027, g32p_row02_traceSegment_023_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2916 54 54, g32p_row02_traceSegment_023_2916_0054, g32p_row02_traceSegment_023_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2808 108 108, g32p_row02_traceSegment_023_2808_0108, g32p_row02_traceSegment_023_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_023 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2592 216 216, g32p_row02_traceSegment_023_2592_0216, g32p_row02_traceSegment_023_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3024 13 14, g32p_row02_traceSegment_023_3024_0013, g32p_row02_traceSegment_023_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3051 13 14, g32p_row02_traceSegment_023_3051_0013, g32p_row02_traceSegment_023_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3024 27 27, g32p_row02_traceSegment_023_3024_0027, g32p_row02_traceSegment_023_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3078 13 14, g32p_row02_traceSegment_023_3078_0013, g32p_row02_traceSegment_023_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3105 13 14, g32p_row02_traceSegment_023_3105_0013, g32p_row02_traceSegment_023_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3078 27 27, g32p_row02_traceSegment_023_3078_0027, g32p_row02_traceSegment_023_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3024 54 54, g32p_row02_traceSegment_023_3024_0054, g32p_row02_traceSegment_023_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3132 13 14, g32p_row02_traceSegment_023_3132_0013, g32p_row02_traceSegment_023_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3159 13 14, g32p_row02_traceSegment_023_3159_0013, g32p_row02_traceSegment_023_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3132 27 27, g32p_row02_traceSegment_023_3132_0027, g32p_row02_traceSegment_023_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3199 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3186 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3186 13 14, g32p_row02_traceSegment_023_3186_0013, g32p_row02_traceSegment_023_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3213 13 14, g32p_row02_traceSegment_023_3213_0013, g32p_row02_traceSegment_023_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 3186 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3186 27 27, g32p_row02_traceSegment_023_3186_0027, g32p_row02_traceSegment_023_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 3132 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3132 54 54, g32p_row02_traceSegment_023_3132_0054, g32p_row02_traceSegment_023_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 3024 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3024 108 108, g32p_row02_traceSegment_023_3024_0108, g32p_row02_traceSegment_023_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3253 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3240 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3240 13 14, g32p_row02_traceSegment_023_3240_0013, g32p_row02_traceSegment_023_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3267 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3267 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3267 13 14, g32p_row02_traceSegment_023_3267_0013, g32p_row02_traceSegment_023_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 3240 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3240 27 27, g32p_row02_traceSegment_023_3240_0027, g32p_row02_traceSegment_023_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3294 13 14, g32p_row02_traceSegment_023_3294_0013, g32p_row02_traceSegment_023_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3321 13 14, g32p_row02_traceSegment_023_3321_0013, g32p_row02_traceSegment_023_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3294 27 27, g32p_row02_traceSegment_023_3294_0027, g32p_row02_traceSegment_023_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 3240 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3240 54 54, g32p_row02_traceSegment_023_3240_0054, g32p_row02_traceSegment_023_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3348 13 14, g32p_row02_traceSegment_023_3348_0013, g32p_row02_traceSegment_023_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3375 13 14, g32p_row02_traceSegment_023_3375_0013, g32p_row02_traceSegment_023_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3348 27 27, g32p_row02_traceSegment_023_3348_0027, g32p_row02_traceSegment_023_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3402 13 14, g32p_row02_traceSegment_023_3402_0013, g32p_row02_traceSegment_023_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_023 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_023 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_023_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_023 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3429 13 14, g32p_row02_traceSegment_023_3429_0013, g32p_row02_traceSegment_023_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_023 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3402 27 27, g32p_row02_traceSegment_023_3402_0027, g32p_row02_traceSegment_023_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_023 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3348 54 54, g32p_row02_traceSegment_023_3348_0054, g32p_row02_traceSegment_023_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_023 3240 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3240 108 108, g32p_row02_traceSegment_023_3240_0108, g32p_row02_traceSegment_023_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_023_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_023 3024 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 3024 216 216, g32p_row02_traceSegment_023_3024_0216, g32p_row02_traceSegment_023_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_023_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_023 2592 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 2592 432 432, g32p_row02_traceSegment_023_2592_0432, g32p_row02_traceSegment_023_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_023_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_023 1728 1728 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 1728 864 864, g32p_row02_traceSegment_023_1728_0864, g32p_row02_traceSegment_023_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_023_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_023 0 3456 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_023 0 1728 1728, g32p_row02_traceSegment_023_0000_1728, g32p_row02_traceSegment_023_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 23 = [0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_023_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_024 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 24 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_024_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 0 13 14, g32p_row02_traceSegment_024_0000_0013, g32p_row02_traceSegment_024_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 27 13 14, g32p_row02_traceSegment_024_0027_0013, g32p_row02_traceSegment_024_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 0 27 27, g32p_row02_traceSegment_024_0000_0027, g32p_row02_traceSegment_024_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 67 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 54 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 54 13 14, g32p_row02_traceSegment_024_0054_0013, g32p_row02_traceSegment_024_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 81 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 81 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 81 13 14, g32p_row02_traceSegment_024_0081_0013, g32p_row02_traceSegment_024_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 54 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 54 27 27, g32p_row02_traceSegment_024_0054_0027, g32p_row02_traceSegment_024_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 0 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 0 54 54, g32p_row02_traceSegment_024_0000_0054, g32p_row02_traceSegment_024_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 108 13 14, g32p_row02_traceSegment_024_0108_0013, g32p_row02_traceSegment_024_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 135 13 14, g32p_row02_traceSegment_024_0135_0013, g32p_row02_traceSegment_024_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 108 27 27, g32p_row02_traceSegment_024_0108_0027, g32p_row02_traceSegment_024_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 162 13 14, g32p_row02_traceSegment_024_0162_0013, g32p_row02_traceSegment_024_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 189 13 14, g32p_row02_traceSegment_024_0189_0013, g32p_row02_traceSegment_024_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 162 27 27, g32p_row02_traceSegment_024_0162_0027, g32p_row02_traceSegment_024_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 108 54 54, g32p_row02_traceSegment_024_0108_0054, g32p_row02_traceSegment_024_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 0 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 0 108 108, g32p_row02_traceSegment_024_0000_0108, g32p_row02_traceSegment_024_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 216 13 14, g32p_row02_traceSegment_024_0216_0013, g32p_row02_traceSegment_024_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 243 13 14, g32p_row02_traceSegment_024_0243_0013, g32p_row02_traceSegment_024_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 216 27 27, g32p_row02_traceSegment_024_0216_0027, g32p_row02_traceSegment_024_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 270 13 14, g32p_row02_traceSegment_024_0270_0013, g32p_row02_traceSegment_024_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 297 13 14, g32p_row02_traceSegment_024_0297_0013, g32p_row02_traceSegment_024_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 270 27 27, g32p_row02_traceSegment_024_0270_0027, g32p_row02_traceSegment_024_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 216 54 54, g32p_row02_traceSegment_024_0216_0054, g32p_row02_traceSegment_024_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 324 13 14, g32p_row02_traceSegment_024_0324_0013, g32p_row02_traceSegment_024_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 351 13 14, g32p_row02_traceSegment_024_0351_0013, g32p_row02_traceSegment_024_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 324 27 27, g32p_row02_traceSegment_024_0324_0027, g32p_row02_traceSegment_024_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 378 13 14, g32p_row02_traceSegment_024_0378_0013, g32p_row02_traceSegment_024_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 405 13 14, g32p_row02_traceSegment_024_0405_0013, g32p_row02_traceSegment_024_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 378 27 27, g32p_row02_traceSegment_024_0378_0027, g32p_row02_traceSegment_024_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 324 54 54, g32p_row02_traceSegment_024_0324_0054, g32p_row02_traceSegment_024_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 216 108 108, g32p_row02_traceSegment_024_0216_0108, g32p_row02_traceSegment_024_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_024 0 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 0 216 216, g32p_row02_traceSegment_024_0000_0216, g32p_row02_traceSegment_024_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 432 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 432 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 432 13 14, g32p_row02_traceSegment_024_0432_0013, g32p_row02_traceSegment_024_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 472 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 459 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 459 13 14, g32p_row02_traceSegment_024_0459_0013, g32p_row02_traceSegment_024_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 432 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 432 27 27, g32p_row02_traceSegment_024_0432_0027, g32p_row02_traceSegment_024_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 486 13 14, g32p_row02_traceSegment_024_0486_0013, g32p_row02_traceSegment_024_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 513 13 14, g32p_row02_traceSegment_024_0513_0013, g32p_row02_traceSegment_024_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 486 27 27, g32p_row02_traceSegment_024_0486_0027, g32p_row02_traceSegment_024_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 432 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 432 54 54, g32p_row02_traceSegment_024_0432_0054, g32p_row02_traceSegment_024_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 540 13 14, g32p_row02_traceSegment_024_0540_0013, g32p_row02_traceSegment_024_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 567 13 14, g32p_row02_traceSegment_024_0567_0013, g32p_row02_traceSegment_024_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 540 27 27, g32p_row02_traceSegment_024_0540_0027, g32p_row02_traceSegment_024_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 594 13 14, g32p_row02_traceSegment_024_0594_0013, g32p_row02_traceSegment_024_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 621 13 14, g32p_row02_traceSegment_024_0621_0013, g32p_row02_traceSegment_024_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 594 27 27, g32p_row02_traceSegment_024_0594_0027, g32p_row02_traceSegment_024_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 540 54 54, g32p_row02_traceSegment_024_0540_0054, g32p_row02_traceSegment_024_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 432 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 432 108 108, g32p_row02_traceSegment_024_0432_0108, g32p_row02_traceSegment_024_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 648 13 14, g32p_row02_traceSegment_024_0648_0013, g32p_row02_traceSegment_024_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 675 13 14, g32p_row02_traceSegment_024_0675_0013, g32p_row02_traceSegment_024_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 648 27 27, g32p_row02_traceSegment_024_0648_0027, g32p_row02_traceSegment_024_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 702 13 14, g32p_row02_traceSegment_024_0702_0013, g32p_row02_traceSegment_024_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 729 13 14, g32p_row02_traceSegment_024_0729_0013, g32p_row02_traceSegment_024_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 702 27 27, g32p_row02_traceSegment_024_0702_0027, g32p_row02_traceSegment_024_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 648 54 54, g32p_row02_traceSegment_024_0648_0054, g32p_row02_traceSegment_024_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 756 13 14, g32p_row02_traceSegment_024_0756_0013, g32p_row02_traceSegment_024_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 783 13 14, g32p_row02_traceSegment_024_0783_0013, g32p_row02_traceSegment_024_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 756 27 27, g32p_row02_traceSegment_024_0756_0027, g32p_row02_traceSegment_024_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 810 13 14, g32p_row02_traceSegment_024_0810_0013, g32p_row02_traceSegment_024_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 837 13 14, g32p_row02_traceSegment_024_0837_0013, g32p_row02_traceSegment_024_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 810 27 27, g32p_row02_traceSegment_024_0810_0027, g32p_row02_traceSegment_024_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 756 54 54, g32p_row02_traceSegment_024_0756_0054, g32p_row02_traceSegment_024_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 648 108 108, g32p_row02_traceSegment_024_0648_0108, g32p_row02_traceSegment_024_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_024 432 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 432 216 216, g32p_row02_traceSegment_024_0432_0216, g32p_row02_traceSegment_024_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_024 0 864 = [0, 0, 2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 0 432 432, g32p_row02_traceSegment_024_0000_0432, g32p_row02_traceSegment_024_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 864 13 14, g32p_row02_traceSegment_024_0864_0013, g32p_row02_traceSegment_024_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 891 13 14, g32p_row02_traceSegment_024_0891_0013, g32p_row02_traceSegment_024_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 864 27 27, g32p_row02_traceSegment_024_0864_0027, g32p_row02_traceSegment_024_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 918 13 14, g32p_row02_traceSegment_024_0918_0013, g32p_row02_traceSegment_024_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 945 13 14, g32p_row02_traceSegment_024_0945_0013, g32p_row02_traceSegment_024_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 918 27 27, g32p_row02_traceSegment_024_0918_0027, g32p_row02_traceSegment_024_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 864 54 54, g32p_row02_traceSegment_024_0864_0054, g32p_row02_traceSegment_024_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 972 13 14, g32p_row02_traceSegment_024_0972_0013, g32p_row02_traceSegment_024_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 999 13 14, g32p_row02_traceSegment_024_0999_0013, g32p_row02_traceSegment_024_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 972 27 27, g32p_row02_traceSegment_024_0972_0027, g32p_row02_traceSegment_024_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1026 13 14, g32p_row02_traceSegment_024_1026_0013, g32p_row02_traceSegment_024_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1053 13 14, g32p_row02_traceSegment_024_1053_0013, g32p_row02_traceSegment_024_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1026 27 27, g32p_row02_traceSegment_024_1026_0027, g32p_row02_traceSegment_024_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 972 54 54, g32p_row02_traceSegment_024_0972_0054, g32p_row02_traceSegment_024_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 864 108 108, g32p_row02_traceSegment_024_0864_0108, g32p_row02_traceSegment_024_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1080 13 14, g32p_row02_traceSegment_024_1080_0013, g32p_row02_traceSegment_024_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1107 13 14, g32p_row02_traceSegment_024_1107_0013, g32p_row02_traceSegment_024_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1080 27 27, g32p_row02_traceSegment_024_1080_0027, g32p_row02_traceSegment_024_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1134 13 14, g32p_row02_traceSegment_024_1134_0013, g32p_row02_traceSegment_024_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1174 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1161 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1161 13 14, g32p_row02_traceSegment_024_1161_0013, g32p_row02_traceSegment_024_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1134 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1134 27 27, g32p_row02_traceSegment_024_1134_0027, g32p_row02_traceSegment_024_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 1080 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1080 54 54, g32p_row02_traceSegment_024_1080_0054, g32p_row02_traceSegment_024_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1201 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1188 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1188 13 14, g32p_row02_traceSegment_024_1188_0013, g32p_row02_traceSegment_024_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1215 13 14, g32p_row02_traceSegment_024_1215_0013, g32p_row02_traceSegment_024_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1188 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1188 27 27, g32p_row02_traceSegment_024_1188_0027, g32p_row02_traceSegment_024_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1255 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1242 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1242 13 14, g32p_row02_traceSegment_024_1242_0013, g32p_row02_traceSegment_024_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1282 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1269 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1269 13 14, g32p_row02_traceSegment_024_1269_0013, g32p_row02_traceSegment_024_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1242 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1242 27 27, g32p_row02_traceSegment_024_1242_0027, g32p_row02_traceSegment_024_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 1188 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1188 54 54, g32p_row02_traceSegment_024_1188_0054, g32p_row02_traceSegment_024_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 1080 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1080 108 108, g32p_row02_traceSegment_024_1080_0108, g32p_row02_traceSegment_024_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_024 864 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 864 216 216, g32p_row02_traceSegment_024_0864_0216, g32p_row02_traceSegment_024_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1296 13 14, g32p_row02_traceSegment_024_1296_0013, g32p_row02_traceSegment_024_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1323 13 14, g32p_row02_traceSegment_024_1323_0013, g32p_row02_traceSegment_024_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1296 27 27, g32p_row02_traceSegment_024_1296_0027, g32p_row02_traceSegment_024_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1350 13 14, g32p_row02_traceSegment_024_1350_0013, g32p_row02_traceSegment_024_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1377 13 14, g32p_row02_traceSegment_024_1377_0013, g32p_row02_traceSegment_024_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1350 27 27, g32p_row02_traceSegment_024_1350_0027, g32p_row02_traceSegment_024_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1296 54 54, g32p_row02_traceSegment_024_1296_0054, g32p_row02_traceSegment_024_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1404 13 14, g32p_row02_traceSegment_024_1404_0013, g32p_row02_traceSegment_024_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1431 13 14, g32p_row02_traceSegment_024_1431_0013, g32p_row02_traceSegment_024_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1404 27 27, g32p_row02_traceSegment_024_1404_0027, g32p_row02_traceSegment_024_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1458 13 14, g32p_row02_traceSegment_024_1458_0013, g32p_row02_traceSegment_024_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1485 13 14, g32p_row02_traceSegment_024_1485_0013, g32p_row02_traceSegment_024_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1458 27 27, g32p_row02_traceSegment_024_1458_0027, g32p_row02_traceSegment_024_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1404 54 54, g32p_row02_traceSegment_024_1404_0054, g32p_row02_traceSegment_024_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1296 108 108, g32p_row02_traceSegment_024_1296_0108, g32p_row02_traceSegment_024_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1512 13 14, g32p_row02_traceSegment_024_1512_0013, g32p_row02_traceSegment_024_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1539 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1539 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1539 13 14, g32p_row02_traceSegment_024_1539_0013, g32p_row02_traceSegment_024_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1512 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1512 27 27, g32p_row02_traceSegment_024_1512_0027, g32p_row02_traceSegment_024_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1579 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1566 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1566 13 14, g32p_row02_traceSegment_024_1566_0013, g32p_row02_traceSegment_024_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1593 13 14, g32p_row02_traceSegment_024_1593_0013, g32p_row02_traceSegment_024_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1566 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1566 27 27, g32p_row02_traceSegment_024_1566_0027, g32p_row02_traceSegment_024_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 1512 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1512 54 54, g32p_row02_traceSegment_024_1512_0054, g32p_row02_traceSegment_024_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1620 13 14, g32p_row02_traceSegment_024_1620_0013, g32p_row02_traceSegment_024_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1647 13 14, g32p_row02_traceSegment_024_1647_0013, g32p_row02_traceSegment_024_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1620 27 27, g32p_row02_traceSegment_024_1620_0027, g32p_row02_traceSegment_024_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1674 13 14, g32p_row02_traceSegment_024_1674_0013, g32p_row02_traceSegment_024_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1701 13 14, g32p_row02_traceSegment_024_1701_0013, g32p_row02_traceSegment_024_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1674 27 27, g32p_row02_traceSegment_024_1674_0027, g32p_row02_traceSegment_024_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1620 54 54, g32p_row02_traceSegment_024_1620_0054, g32p_row02_traceSegment_024_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 1512 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1512 108 108, g32p_row02_traceSegment_024_1512_0108, g32p_row02_traceSegment_024_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_024 1296 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1296 216 216, g32p_row02_traceSegment_024_1296_0216, g32p_row02_traceSegment_024_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_024 864 864 = [0, 0, 4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 864 432 432, g32p_row02_traceSegment_024_0864_0432, g32p_row02_traceSegment_024_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_024 0 1728 = [0, 0, 6, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 0 864 864, g32p_row02_traceSegment_024_0000_0864, g32p_row02_traceSegment_024_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1728 13 14, g32p_row02_traceSegment_024_1728_0013, g32p_row02_traceSegment_024_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1755 13 14, g32p_row02_traceSegment_024_1755_0013, g32p_row02_traceSegment_024_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1728 27 27, g32p_row02_traceSegment_024_1728_0027, g32p_row02_traceSegment_024_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1782 13 14, g32p_row02_traceSegment_024_1782_0013, g32p_row02_traceSegment_024_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1809 13 14, g32p_row02_traceSegment_024_1809_0013, g32p_row02_traceSegment_024_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1782 27 27, g32p_row02_traceSegment_024_1782_0027, g32p_row02_traceSegment_024_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1728 54 54, g32p_row02_traceSegment_024_1728_0054, g32p_row02_traceSegment_024_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1836 13 14, g32p_row02_traceSegment_024_1836_0013, g32p_row02_traceSegment_024_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1863 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1863 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1863 13 14, g32p_row02_traceSegment_024_1863_0013, g32p_row02_traceSegment_024_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1836 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1836 27 27, g32p_row02_traceSegment_024_1836_0027, g32p_row02_traceSegment_024_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1890 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1890 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1890 13 14, g32p_row02_traceSegment_024_1890_0013, g32p_row02_traceSegment_024_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1917 13 14, g32p_row02_traceSegment_024_1917_0013, g32p_row02_traceSegment_024_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1890 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1890 27 27, g32p_row02_traceSegment_024_1890_0027, g32p_row02_traceSegment_024_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 1836 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1836 54 54, g32p_row02_traceSegment_024_1836_0054, g32p_row02_traceSegment_024_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 1728 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1728 108 108, g32p_row02_traceSegment_024_1728_0108, g32p_row02_traceSegment_024_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1944 13 14, g32p_row02_traceSegment_024_1944_0013, g32p_row02_traceSegment_024_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1971 13 14, g32p_row02_traceSegment_024_1971_0013, g32p_row02_traceSegment_024_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1944 27 27, g32p_row02_traceSegment_024_1944_0027, g32p_row02_traceSegment_024_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1998 13 14, g32p_row02_traceSegment_024_1998_0013, g32p_row02_traceSegment_024_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2025 13 14, g32p_row02_traceSegment_024_2025_0013, g32p_row02_traceSegment_024_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1998 27 27, g32p_row02_traceSegment_024_1998_0027, g32p_row02_traceSegment_024_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1944 54 54, g32p_row02_traceSegment_024_1944_0054, g32p_row02_traceSegment_024_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2052 13 14, g32p_row02_traceSegment_024_2052_0013, g32p_row02_traceSegment_024_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2079 13 14, g32p_row02_traceSegment_024_2079_0013, g32p_row02_traceSegment_024_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2052 27 27, g32p_row02_traceSegment_024_2052_0027, g32p_row02_traceSegment_024_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2106 13 14, g32p_row02_traceSegment_024_2106_0013, g32p_row02_traceSegment_024_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2133 13 14, g32p_row02_traceSegment_024_2133_0013, g32p_row02_traceSegment_024_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2106 27 27, g32p_row02_traceSegment_024_2106_0027, g32p_row02_traceSegment_024_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2052 54 54, g32p_row02_traceSegment_024_2052_0054, g32p_row02_traceSegment_024_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1944 108 108, g32p_row02_traceSegment_024_1944_0108, g32p_row02_traceSegment_024_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_024 1728 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1728 216 216, g32p_row02_traceSegment_024_1728_0216, g32p_row02_traceSegment_024_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2160 13 14, g32p_row02_traceSegment_024_2160_0013, g32p_row02_traceSegment_024_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2200 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2187 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2187 13 14, g32p_row02_traceSegment_024_2187_0013, g32p_row02_traceSegment_024_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2160 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2160 27 27, g32p_row02_traceSegment_024_2160_0027, g32p_row02_traceSegment_024_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2214 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2214 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2214 13 14, g32p_row02_traceSegment_024_2214_0013, g32p_row02_traceSegment_024_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2241 13 14, g32p_row02_traceSegment_024_2241_0013, g32p_row02_traceSegment_024_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2214 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2214 27 27, g32p_row02_traceSegment_024_2214_0027, g32p_row02_traceSegment_024_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 2160 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2160 54 54, g32p_row02_traceSegment_024_2160_0054, g32p_row02_traceSegment_024_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2268 13 14, g32p_row02_traceSegment_024_2268_0013, g32p_row02_traceSegment_024_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2295 13 14, g32p_row02_traceSegment_024_2295_0013, g32p_row02_traceSegment_024_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2268 27 27, g32p_row02_traceSegment_024_2268_0027, g32p_row02_traceSegment_024_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2322 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2322 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2322 13 14, g32p_row02_traceSegment_024_2322_0013, g32p_row02_traceSegment_024_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2349 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2362 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2349 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2349 13 14, g32p_row02_traceSegment_024_2349_0013, g32p_row02_traceSegment_024_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2322 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2322 27 27, g32p_row02_traceSegment_024_2322_0027, g32p_row02_traceSegment_024_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 2268 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2268 54 54, g32p_row02_traceSegment_024_2268_0054, g32p_row02_traceSegment_024_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 2160 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2160 108 108, g32p_row02_traceSegment_024_2160_0108, g32p_row02_traceSegment_024_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2389 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2376 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2376 13 14, g32p_row02_traceSegment_024_2376_0013, g32p_row02_traceSegment_024_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2403 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2403 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2403 13 14, g32p_row02_traceSegment_024_2403_0013, g32p_row02_traceSegment_024_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2376 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2376 27 27, g32p_row02_traceSegment_024_2376_0027, g32p_row02_traceSegment_024_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2430 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2443 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2430 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2430 13 14, g32p_row02_traceSegment_024_2430_0013, g32p_row02_traceSegment_024_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2457 13 14, g32p_row02_traceSegment_024_2457_0013, g32p_row02_traceSegment_024_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2430 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2430 27 27, g32p_row02_traceSegment_024_2430_0027, g32p_row02_traceSegment_024_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 2376 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2376 54 54, g32p_row02_traceSegment_024_2376_0054, g32p_row02_traceSegment_024_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2484 13 14, g32p_row02_traceSegment_024_2484_0013, g32p_row02_traceSegment_024_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2511 13 14, g32p_row02_traceSegment_024_2511_0013, g32p_row02_traceSegment_024_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2484 27 27, g32p_row02_traceSegment_024_2484_0027, g32p_row02_traceSegment_024_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2538 13 14, g32p_row02_traceSegment_024_2538_0013, g32p_row02_traceSegment_024_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2565 13 14, g32p_row02_traceSegment_024_2565_0013, g32p_row02_traceSegment_024_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2538 27 27, g32p_row02_traceSegment_024_2538_0027, g32p_row02_traceSegment_024_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2484 54 54, g32p_row02_traceSegment_024_2484_0054, g32p_row02_traceSegment_024_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 2376 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2376 108 108, g32p_row02_traceSegment_024_2376_0108, g32p_row02_traceSegment_024_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_024 2160 432 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2160 216 216, g32p_row02_traceSegment_024_2160_0216, g32p_row02_traceSegment_024_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_024 1728 864 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1728 432 432, g32p_row02_traceSegment_024_1728_0432, g32p_row02_traceSegment_024_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2592 13 14, g32p_row02_traceSegment_024_2592_0013, g32p_row02_traceSegment_024_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2619 13 14, g32p_row02_traceSegment_024_2619_0013, g32p_row02_traceSegment_024_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2592 27 27, g32p_row02_traceSegment_024_2592_0027, g32p_row02_traceSegment_024_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2646 13 14, g32p_row02_traceSegment_024_2646_0013, g32p_row02_traceSegment_024_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2673 13 14, g32p_row02_traceSegment_024_2673_0013, g32p_row02_traceSegment_024_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2646 27 27, g32p_row02_traceSegment_024_2646_0027, g32p_row02_traceSegment_024_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2592 54 54, g32p_row02_traceSegment_024_2592_0054, g32p_row02_traceSegment_024_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2700 13 14, g32p_row02_traceSegment_024_2700_0013, g32p_row02_traceSegment_024_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2727 13 14, g32p_row02_traceSegment_024_2727_0013, g32p_row02_traceSegment_024_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2700 27 27, g32p_row02_traceSegment_024_2700_0027, g32p_row02_traceSegment_024_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2754 13 14, g32p_row02_traceSegment_024_2754_0013, g32p_row02_traceSegment_024_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2781 13 14, g32p_row02_traceSegment_024_2781_0013, g32p_row02_traceSegment_024_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2754 27 27, g32p_row02_traceSegment_024_2754_0027, g32p_row02_traceSegment_024_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2700 54 54, g32p_row02_traceSegment_024_2700_0054, g32p_row02_traceSegment_024_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2592 108 108, g32p_row02_traceSegment_024_2592_0108, g32p_row02_traceSegment_024_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2808 13 14, g32p_row02_traceSegment_024_2808_0013, g32p_row02_traceSegment_024_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2835 13 14, g32p_row02_traceSegment_024_2835_0013, g32p_row02_traceSegment_024_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2808 27 27, g32p_row02_traceSegment_024_2808_0027, g32p_row02_traceSegment_024_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2862 13 14, g32p_row02_traceSegment_024_2862_0013, g32p_row02_traceSegment_024_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2889 13 14, g32p_row02_traceSegment_024_2889_0013, g32p_row02_traceSegment_024_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2862 27 27, g32p_row02_traceSegment_024_2862_0027, g32p_row02_traceSegment_024_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2808 54 54, g32p_row02_traceSegment_024_2808_0054, g32p_row02_traceSegment_024_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2916 13 14, g32p_row02_traceSegment_024_2916_0013, g32p_row02_traceSegment_024_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2943 13 14, g32p_row02_traceSegment_024_2943_0013, g32p_row02_traceSegment_024_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2916 27 27, g32p_row02_traceSegment_024_2916_0027, g32p_row02_traceSegment_024_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2970 13 14, g32p_row02_traceSegment_024_2970_0013, g32p_row02_traceSegment_024_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2997 13 14, g32p_row02_traceSegment_024_2997_0013, g32p_row02_traceSegment_024_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2970 27 27, g32p_row02_traceSegment_024_2970_0027, g32p_row02_traceSegment_024_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2916 54 54, g32p_row02_traceSegment_024_2916_0054, g32p_row02_traceSegment_024_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2808 108 108, g32p_row02_traceSegment_024_2808_0108, g32p_row02_traceSegment_024_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_024 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2592 216 216, g32p_row02_traceSegment_024_2592_0216, g32p_row02_traceSegment_024_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3024 13 14, g32p_row02_traceSegment_024_3024_0013, g32p_row02_traceSegment_024_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3051 13 14, g32p_row02_traceSegment_024_3051_0013, g32p_row02_traceSegment_024_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3024 27 27, g32p_row02_traceSegment_024_3024_0027, g32p_row02_traceSegment_024_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3078 13 14, g32p_row02_traceSegment_024_3078_0013, g32p_row02_traceSegment_024_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3105 13 14, g32p_row02_traceSegment_024_3105_0013, g32p_row02_traceSegment_024_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3078 27 27, g32p_row02_traceSegment_024_3078_0027, g32p_row02_traceSegment_024_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3024 54 54, g32p_row02_traceSegment_024_3024_0054, g32p_row02_traceSegment_024_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3132 13 14, g32p_row02_traceSegment_024_3132_0013, g32p_row02_traceSegment_024_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3159 13 14, g32p_row02_traceSegment_024_3159_0013, g32p_row02_traceSegment_024_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3132 27 27, g32p_row02_traceSegment_024_3132_0027, g32p_row02_traceSegment_024_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3186 13 14, g32p_row02_traceSegment_024_3186_0013, g32p_row02_traceSegment_024_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3226 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3213 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3213 13 14, g32p_row02_traceSegment_024_3213_0013, g32p_row02_traceSegment_024_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 3186 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3186 27 27, g32p_row02_traceSegment_024_3186_0027, g32p_row02_traceSegment_024_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 3132 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3132 54 54, g32p_row02_traceSegment_024_3132_0054, g32p_row02_traceSegment_024_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 3024 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3024 108 108, g32p_row02_traceSegment_024_3024_0108, g32p_row02_traceSegment_024_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3240 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3240 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3240 13 14, g32p_row02_traceSegment_024_3240_0013, g32p_row02_traceSegment_024_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3267 13 14, g32p_row02_traceSegment_024_3267_0013, g32p_row02_traceSegment_024_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 3240 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3240 27 27, g32p_row02_traceSegment_024_3240_0027, g32p_row02_traceSegment_024_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3294 13 14, g32p_row02_traceSegment_024_3294_0013, g32p_row02_traceSegment_024_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3334 14 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3321 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3321 13 14, g32p_row02_traceSegment_024_3321_0013, g32p_row02_traceSegment_024_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 3294 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3294 27 27, g32p_row02_traceSegment_024_3294_0027, g32p_row02_traceSegment_024_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 3240 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3240 54 54, g32p_row02_traceSegment_024_3240_0054, g32p_row02_traceSegment_024_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3348 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3361 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3348 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3348 13 14, g32p_row02_traceSegment_024_3348_0013, g32p_row02_traceSegment_024_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3375 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3375 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3375 13 14, g32p_row02_traceSegment_024_3375_0013, g32p_row02_traceSegment_024_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 3348 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3348 27 27, g32p_row02_traceSegment_024_3348_0027, g32p_row02_traceSegment_024_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3402 13 14, g32p_row02_traceSegment_024_3402_0013, g32p_row02_traceSegment_024_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_024 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_024 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_024_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_024 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3429 13 14, g32p_row02_traceSegment_024_3429_0013, g32p_row02_traceSegment_024_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_024 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3402 27 27, g32p_row02_traceSegment_024_3402_0027, g32p_row02_traceSegment_024_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_024 3348 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3348 54 54, g32p_row02_traceSegment_024_3348_0054, g32p_row02_traceSegment_024_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_024 3240 216 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3240 108 108, g32p_row02_traceSegment_024_3240_0108, g32p_row02_traceSegment_024_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_024_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_024 3024 432 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 3024 216 216, g32p_row02_traceSegment_024_3024_0216, g32p_row02_traceSegment_024_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_024_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_024 2592 864 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 2592 432 432, g32p_row02_traceSegment_024_2592_0432, g32p_row02_traceSegment_024_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_024_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_024 1728 1728 = [0, 0, 10, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 1728 864 864, g32p_row02_traceSegment_024_1728_0864, g32p_row02_traceSegment_024_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_024_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_024 0 3456 = [0, 0, 16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_024 0 1728 1728, g32p_row02_traceSegment_024_0000_1728, g32p_row02_traceSegment_024_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 24 = [0, 0, 16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_024_0000_3456

end HodgeLean.Foundations.Program

end
end
