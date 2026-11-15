import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_074 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 74 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_074_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 0 13 14, g32p_row02_traceSegment_074_0000_0013, g32p_row02_traceSegment_074_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 27 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 40 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 27 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 27 13 14, g32p_row02_traceSegment_074_0027_0013, g32p_row02_traceSegment_074_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 0 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 0 27 27, g32p_row02_traceSegment_074_0000_0027, g32p_row02_traceSegment_074_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 54 13 14, g32p_row02_traceSegment_074_0054_0013, g32p_row02_traceSegment_074_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 81 13 14, g32p_row02_traceSegment_074_0081_0013, g32p_row02_traceSegment_074_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 54 27 27, g32p_row02_traceSegment_074_0054_0027, g32p_row02_traceSegment_074_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 0 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 0 54 54, g32p_row02_traceSegment_074_0000_0054, g32p_row02_traceSegment_074_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 108 13 14, g32p_row02_traceSegment_074_0108_0013, g32p_row02_traceSegment_074_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 135 13 14, g32p_row02_traceSegment_074_0135_0013, g32p_row02_traceSegment_074_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 108 27 27, g32p_row02_traceSegment_074_0108_0027, g32p_row02_traceSegment_074_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 162 13 14, g32p_row02_traceSegment_074_0162_0013, g32p_row02_traceSegment_074_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 189 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 189 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 189 13 14, g32p_row02_traceSegment_074_0189_0013, g32p_row02_traceSegment_074_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 162 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 162 27 27, g32p_row02_traceSegment_074_0162_0027, g32p_row02_traceSegment_074_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 108 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 108 54 54, g32p_row02_traceSegment_074_0108_0054, g32p_row02_traceSegment_074_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 0 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 0 108 108, g32p_row02_traceSegment_074_0000_0108, g32p_row02_traceSegment_074_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 216 13 14, g32p_row02_traceSegment_074_0216_0013, g32p_row02_traceSegment_074_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 243 13 14, g32p_row02_traceSegment_074_0243_0013, g32p_row02_traceSegment_074_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 216 27 27, g32p_row02_traceSegment_074_0216_0027, g32p_row02_traceSegment_074_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 283 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 270 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 270 13 14, g32p_row02_traceSegment_074_0270_0013, g32p_row02_traceSegment_074_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 297 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 310 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 297 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 297 13 14, g32p_row02_traceSegment_074_0297_0013, g32p_row02_traceSegment_074_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 270 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 270 27 27, g32p_row02_traceSegment_074_0270_0027, g32p_row02_traceSegment_074_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 216 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 216 54 54, g32p_row02_traceSegment_074_0216_0054, g32p_row02_traceSegment_074_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 324 13 14, g32p_row02_traceSegment_074_0324_0013, g32p_row02_traceSegment_074_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 351 13 14, g32p_row02_traceSegment_074_0351_0013, g32p_row02_traceSegment_074_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 324 27 27, g32p_row02_traceSegment_074_0324_0027, g32p_row02_traceSegment_074_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 378 13 14, g32p_row02_traceSegment_074_0378_0013, g32p_row02_traceSegment_074_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 405 13 14, g32p_row02_traceSegment_074_0405_0013, g32p_row02_traceSegment_074_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 378 27 27, g32p_row02_traceSegment_074_0378_0027, g32p_row02_traceSegment_074_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 324 54 54, g32p_row02_traceSegment_074_0324_0054, g32p_row02_traceSegment_074_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 216 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 216 108 108, g32p_row02_traceSegment_074_0216_0108, g32p_row02_traceSegment_074_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_074 0 432 = [0, 3, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 0 216 216, g32p_row02_traceSegment_074_0000_0216, g32p_row02_traceSegment_074_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 432 13 14, g32p_row02_traceSegment_074_0432_0013, g32p_row02_traceSegment_074_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 459 13 14, g32p_row02_traceSegment_074_0459_0013, g32p_row02_traceSegment_074_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 432 27 27, g32p_row02_traceSegment_074_0432_0027, g32p_row02_traceSegment_074_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 499 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 486 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 486 13 14, g32p_row02_traceSegment_074_0486_0013, g32p_row02_traceSegment_074_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 513 13 14, g32p_row02_traceSegment_074_0513_0013, g32p_row02_traceSegment_074_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 486 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 486 27 27, g32p_row02_traceSegment_074_0486_0027, g32p_row02_traceSegment_074_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 432 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 432 54 54, g32p_row02_traceSegment_074_0432_0054, g32p_row02_traceSegment_074_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 540 13 14, g32p_row02_traceSegment_074_0540_0013, g32p_row02_traceSegment_074_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 567 13 14, g32p_row02_traceSegment_074_0567_0013, g32p_row02_traceSegment_074_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 540 27 27, g32p_row02_traceSegment_074_0540_0027, g32p_row02_traceSegment_074_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 594 13 14, g32p_row02_traceSegment_074_0594_0013, g32p_row02_traceSegment_074_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 621 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 634 14 = [0, 4, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 621 27 = [0, 6, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 621 13 14, g32p_row02_traceSegment_074_0621_0013, g32p_row02_traceSegment_074_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 594 54 = [0, 6, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 594 27 27, g32p_row02_traceSegment_074_0594_0027, g32p_row02_traceSegment_074_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 540 108 = [0, 6, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 540 54 54, g32p_row02_traceSegment_074_0540_0054, g32p_row02_traceSegment_074_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 432 216 = [0, 8, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 432 108 108, g32p_row02_traceSegment_074_0432_0108, g32p_row02_traceSegment_074_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 648 13 = [0, 3, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 661 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 648 27 = [0, 7, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 648 13 14, g32p_row02_traceSegment_074_0648_0013, g32p_row02_traceSegment_074_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 675 13 = [0, 1, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 688 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 675 27 = [0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 675 13 14, g32p_row02_traceSegment_074_0675_0013, g32p_row02_traceSegment_074_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 648 54 = [0, 10, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 648 27 27, g32p_row02_traceSegment_074_0648_0027, g32p_row02_traceSegment_074_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 702 13 14, g32p_row02_traceSegment_074_0702_0013, g32p_row02_traceSegment_074_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 742 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 729 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 729 13 14, g32p_row02_traceSegment_074_0729_0013, g32p_row02_traceSegment_074_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 702 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 702 27 27, g32p_row02_traceSegment_074_0702_0027, g32p_row02_traceSegment_074_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 648 108 = [0, 14, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 648 54 54, g32p_row02_traceSegment_074_0648_0054, g32p_row02_traceSegment_074_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 769 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 756 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 756 13 14, g32p_row02_traceSegment_074_0756_0013, g32p_row02_traceSegment_074_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 783 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 783 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 783 13 14, g32p_row02_traceSegment_074_0783_0013, g32p_row02_traceSegment_074_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 756 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 756 27 27, g32p_row02_traceSegment_074_0756_0027, g32p_row02_traceSegment_074_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 810 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 823 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 810 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 810 13 14, g32p_row02_traceSegment_074_0810_0013, g32p_row02_traceSegment_074_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 837 13 14, g32p_row02_traceSegment_074_0837_0013, g32p_row02_traceSegment_074_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 810 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 810 27 27, g32p_row02_traceSegment_074_0810_0027, g32p_row02_traceSegment_074_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 756 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 756 54 54, g32p_row02_traceSegment_074_0756_0054, g32p_row02_traceSegment_074_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 648 216 = [0, 22, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 648 108 108, g32p_row02_traceSegment_074_0648_0108, g32p_row02_traceSegment_074_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_074 432 432 = [0, 30, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 432 216 216, g32p_row02_traceSegment_074_0432_0216, g32p_row02_traceSegment_074_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_074 0 864 = [0, 33, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 0 432 432, g32p_row02_traceSegment_074_0000_0432, g32p_row02_traceSegment_074_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 877 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 864 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 864 13 14, g32p_row02_traceSegment_074_0864_0013, g32p_row02_traceSegment_074_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 891 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 891 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 891 13 14, g32p_row02_traceSegment_074_0891_0013, g32p_row02_traceSegment_074_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 864 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 864 27 27, g32p_row02_traceSegment_074_0864_0027, g32p_row02_traceSegment_074_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 931 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 918 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 918 13 14, g32p_row02_traceSegment_074_0918_0013, g32p_row02_traceSegment_074_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 945 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 945 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 945 13 14, g32p_row02_traceSegment_074_0945_0013, g32p_row02_traceSegment_074_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 918 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 918 27 27, g32p_row02_traceSegment_074_0918_0027, g32p_row02_traceSegment_074_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 864 108 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 864 54 54, g32p_row02_traceSegment_074_0864_0054, g32p_row02_traceSegment_074_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 972 13 = [0, 3, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 985 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 972 27 = [0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 972 13 14, g32p_row02_traceSegment_074_0972_0013, g32p_row02_traceSegment_074_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 999 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 999 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 999 13 14, g32p_row02_traceSegment_074_0999_0013, g32p_row02_traceSegment_074_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 972 54 = [0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 972 27 27, g32p_row02_traceSegment_074_0972_0027, g32p_row02_traceSegment_074_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1039 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1026 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1026 13 14, g32p_row02_traceSegment_074_1026_0013, g32p_row02_traceSegment_074_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1053 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1053 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1053 13 14, g32p_row02_traceSegment_074_1053_0013, g32p_row02_traceSegment_074_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1026 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1026 27 27, g32p_row02_traceSegment_074_1026_0027, g32p_row02_traceSegment_074_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 972 108 = [0, 8, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 972 54 54, g32p_row02_traceSegment_074_0972_0054, g32p_row02_traceSegment_074_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 864 216 = [0, 15, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 864 108 108, g32p_row02_traceSegment_074_0864_0108, g32p_row02_traceSegment_074_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1080 13 14, g32p_row02_traceSegment_074_1080_0013, g32p_row02_traceSegment_074_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1107 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1120 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1107 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1107 13 14, g32p_row02_traceSegment_074_1107_0013, g32p_row02_traceSegment_074_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1080 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1080 27 27, g32p_row02_traceSegment_074_1080_0027, g32p_row02_traceSegment_074_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1134 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1134 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1134 13 14, g32p_row02_traceSegment_074_1134_0013, g32p_row02_traceSegment_074_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1161 13 14, g32p_row02_traceSegment_074_1161_0013, g32p_row02_traceSegment_074_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1134 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1134 27 27, g32p_row02_traceSegment_074_1134_0027, g32p_row02_traceSegment_074_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 1080 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1080 54 54, g32p_row02_traceSegment_074_1080_0054, g32p_row02_traceSegment_074_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1201 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1188 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1188 13 14, g32p_row02_traceSegment_074_1188_0013, g32p_row02_traceSegment_074_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1215 13 14, g32p_row02_traceSegment_074_1215_0013, g32p_row02_traceSegment_074_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1188 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1188 27 27, g32p_row02_traceSegment_074_1188_0027, g32p_row02_traceSegment_074_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1242 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1242 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1242 13 14, g32p_row02_traceSegment_074_1242_0013, g32p_row02_traceSegment_074_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1269 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1282 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1269 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1269 13 14, g32p_row02_traceSegment_074_1269_0013, g32p_row02_traceSegment_074_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1242 54 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1242 27 27, g32p_row02_traceSegment_074_1242_0027, g32p_row02_traceSegment_074_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 1188 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1188 54 54, g32p_row02_traceSegment_074_1188_0054, g32p_row02_traceSegment_074_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 1080 216 = [0, 4, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1080 108 108, g32p_row02_traceSegment_074_1080_0108, g32p_row02_traceSegment_074_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_074 864 432 = [0, 19, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 864 216 216, g32p_row02_traceSegment_074_0864_0216, g32p_row02_traceSegment_074_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1296 13 14, g32p_row02_traceSegment_074_1296_0013, g32p_row02_traceSegment_074_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1336 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1323 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1323 13 14, g32p_row02_traceSegment_074_1323_0013, g32p_row02_traceSegment_074_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1296 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1296 27 27, g32p_row02_traceSegment_074_1296_0027, g32p_row02_traceSegment_074_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1363 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1350 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1350 13 14, g32p_row02_traceSegment_074_1350_0013, g32p_row02_traceSegment_074_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1377 13 14, g32p_row02_traceSegment_074_1377_0013, g32p_row02_traceSegment_074_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1350 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1350 27 27, g32p_row02_traceSegment_074_1350_0027, g32p_row02_traceSegment_074_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 1296 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1296 54 54, g32p_row02_traceSegment_074_1296_0054, g32p_row02_traceSegment_074_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1404 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1404 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1404 13 14, g32p_row02_traceSegment_074_1404_0013, g32p_row02_traceSegment_074_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1444 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1431 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1431 13 14, g32p_row02_traceSegment_074_1431_0013, g32p_row02_traceSegment_074_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1404 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1404 27 27, g32p_row02_traceSegment_074_1404_0027, g32p_row02_traceSegment_074_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1458 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1471 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1458 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1458 13 14, g32p_row02_traceSegment_074_1458_0013, g32p_row02_traceSegment_074_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1485 13 14, g32p_row02_traceSegment_074_1485_0013, g32p_row02_traceSegment_074_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1458 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1458 27 27, g32p_row02_traceSegment_074_1458_0027, g32p_row02_traceSegment_074_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 1404 108 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1404 54 54, g32p_row02_traceSegment_074_1404_0054, g32p_row02_traceSegment_074_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 1296 216 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1296 108 108, g32p_row02_traceSegment_074_1296_0108, g32p_row02_traceSegment_074_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1512 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1525 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1512 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1512 13 14, g32p_row02_traceSegment_074_1512_0013, g32p_row02_traceSegment_074_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1539 13 14, g32p_row02_traceSegment_074_1539_0013, g32p_row02_traceSegment_074_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1512 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1512 27 27, g32p_row02_traceSegment_074_1512_0027, g32p_row02_traceSegment_074_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1566 13 14, g32p_row02_traceSegment_074_1566_0013, g32p_row02_traceSegment_074_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1593 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1593 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1593 13 14, g32p_row02_traceSegment_074_1593_0013, g32p_row02_traceSegment_074_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1566 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1566 27 27, g32p_row02_traceSegment_074_1566_0027, g32p_row02_traceSegment_074_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 1512 108 = [0, 5, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1512 54 54, g32p_row02_traceSegment_074_1512_0054, g32p_row02_traceSegment_074_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1620 13 14, g32p_row02_traceSegment_074_1620_0013, g32p_row02_traceSegment_074_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1647 13 14, g32p_row02_traceSegment_074_1647_0013, g32p_row02_traceSegment_074_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1620 27 27, g32p_row02_traceSegment_074_1620_0027, g32p_row02_traceSegment_074_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1674 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1687 14 = [0, 1, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1674 27 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1674 13 14, g32p_row02_traceSegment_074_1674_0013, g32p_row02_traceSegment_074_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1714 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1701 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1701 13 14, g32p_row02_traceSegment_074_1701_0013, g32p_row02_traceSegment_074_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1674 54 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1674 27 27, g32p_row02_traceSegment_074_1674_0027, g32p_row02_traceSegment_074_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 1620 108 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1620 54 54, g32p_row02_traceSegment_074_1620_0054, g32p_row02_traceSegment_074_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 1512 216 = [0, 7, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1512 108 108, g32p_row02_traceSegment_074_1512_0108, g32p_row02_traceSegment_074_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_074 1296 432 = [0, 18, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1296 216 216, g32p_row02_traceSegment_074_1296_0216, g32p_row02_traceSegment_074_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_074 864 864 = [0, 37, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 864 432 432, g32p_row02_traceSegment_074_0864_0432, g32p_row02_traceSegment_074_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_074 0 1728 = [0, 70, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 0 864 864, g32p_row02_traceSegment_074_0000_0864, g32p_row02_traceSegment_074_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1728 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1741 14 = [0, 2, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1728 27 = [0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1728 13 14, g32p_row02_traceSegment_074_1728_0013, g32p_row02_traceSegment_074_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1755 13 = [0, 1, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1755 27 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1755 13 14, g32p_row02_traceSegment_074_1755_0013, g32p_row02_traceSegment_074_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1728 54 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1728 27 27, g32p_row02_traceSegment_074_1728_0027, g32p_row02_traceSegment_074_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1782 13 14, g32p_row02_traceSegment_074_1782_0013, g32p_row02_traceSegment_074_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1809 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1809 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1809 13 14, g32p_row02_traceSegment_074_1809_0013, g32p_row02_traceSegment_074_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1782 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1782 27 27, g32p_row02_traceSegment_074_1782_0027, g32p_row02_traceSegment_074_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 1728 108 = [0, 6, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1728 54 54, g32p_row02_traceSegment_074_1728_0054, g32p_row02_traceSegment_074_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1836 13 14, g32p_row02_traceSegment_074_1836_0013, g32p_row02_traceSegment_074_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1863 13 14, g32p_row02_traceSegment_074_1863_0013, g32p_row02_traceSegment_074_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1836 27 27, g32p_row02_traceSegment_074_1836_0027, g32p_row02_traceSegment_074_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1903 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1890 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1890 13 14, g32p_row02_traceSegment_074_1890_0013, g32p_row02_traceSegment_074_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1917 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1930 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1917 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1917 13 14, g32p_row02_traceSegment_074_1917_0013, g32p_row02_traceSegment_074_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1890 54 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1890 27 27, g32p_row02_traceSegment_074_1890_0027, g32p_row02_traceSegment_074_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 1836 108 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1836 54 54, g32p_row02_traceSegment_074_1836_0054, g32p_row02_traceSegment_074_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 1728 216 = [0, 12, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1728 108 108, g32p_row02_traceSegment_074_1728_0108, g32p_row02_traceSegment_074_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1944 13 14, g32p_row02_traceSegment_074_1944_0013, g32p_row02_traceSegment_074_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1971 13 14, g32p_row02_traceSegment_074_1971_0013, g32p_row02_traceSegment_074_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1944 27 27, g32p_row02_traceSegment_074_1944_0027, g32p_row02_traceSegment_074_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1998 13 14, g32p_row02_traceSegment_074_1998_0013, g32p_row02_traceSegment_074_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2025 13 14, g32p_row02_traceSegment_074_2025_0013, g32p_row02_traceSegment_074_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1998 27 27, g32p_row02_traceSegment_074_1998_0027, g32p_row02_traceSegment_074_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1944 54 54, g32p_row02_traceSegment_074_1944_0054, g32p_row02_traceSegment_074_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2052 13 14, g32p_row02_traceSegment_074_2052_0013, g32p_row02_traceSegment_074_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2079 13 14, g32p_row02_traceSegment_074_2079_0013, g32p_row02_traceSegment_074_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2052 27 27, g32p_row02_traceSegment_074_2052_0027, g32p_row02_traceSegment_074_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2106 13 14, g32p_row02_traceSegment_074_2106_0013, g32p_row02_traceSegment_074_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2146 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2133 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2133 13 14, g32p_row02_traceSegment_074_2133_0013, g32p_row02_traceSegment_074_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2106 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2106 27 27, g32p_row02_traceSegment_074_2106_0027, g32p_row02_traceSegment_074_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 2052 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2052 54 54, g32p_row02_traceSegment_074_2052_0054, g32p_row02_traceSegment_074_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 1944 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1944 108 108, g32p_row02_traceSegment_074_1944_0108, g32p_row02_traceSegment_074_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_074 1728 432 = [0, 12, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1728 216 216, g32p_row02_traceSegment_074_1728_0216, g32p_row02_traceSegment_074_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2160 13 14, g32p_row02_traceSegment_074_2160_0013, g32p_row02_traceSegment_074_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2187 13 14, g32p_row02_traceSegment_074_2187_0013, g32p_row02_traceSegment_074_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2160 27 27, g32p_row02_traceSegment_074_2160_0027, g32p_row02_traceSegment_074_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2214 13 14, g32p_row02_traceSegment_074_2214_0013, g32p_row02_traceSegment_074_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2241 13 14, g32p_row02_traceSegment_074_2241_0013, g32p_row02_traceSegment_074_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2214 27 27, g32p_row02_traceSegment_074_2214_0027, g32p_row02_traceSegment_074_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2160 54 54, g32p_row02_traceSegment_074_2160_0054, g32p_row02_traceSegment_074_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2268 13 14, g32p_row02_traceSegment_074_2268_0013, g32p_row02_traceSegment_074_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2295 13 14, g32p_row02_traceSegment_074_2295_0013, g32p_row02_traceSegment_074_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2268 27 27, g32p_row02_traceSegment_074_2268_0027, g32p_row02_traceSegment_074_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2322 13 14, g32p_row02_traceSegment_074_2322_0013, g32p_row02_traceSegment_074_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2362 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2349 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2349 13 14, g32p_row02_traceSegment_074_2349_0013, g32p_row02_traceSegment_074_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2322 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2322 27 27, g32p_row02_traceSegment_074_2322_0027, g32p_row02_traceSegment_074_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 2268 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2268 54 54, g32p_row02_traceSegment_074_2268_0054, g32p_row02_traceSegment_074_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 2160 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2160 108 108, g32p_row02_traceSegment_074_2160_0108, g32p_row02_traceSegment_074_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2376 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2376 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2376 13 14, g32p_row02_traceSegment_074_2376_0013, g32p_row02_traceSegment_074_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2403 13 14, g32p_row02_traceSegment_074_2403_0013, g32p_row02_traceSegment_074_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2376 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2376 27 27, g32p_row02_traceSegment_074_2376_0027, g32p_row02_traceSegment_074_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2430 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2430 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2430 13 14, g32p_row02_traceSegment_074_2430_0013, g32p_row02_traceSegment_074_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2457 13 14, g32p_row02_traceSegment_074_2457_0013, g32p_row02_traceSegment_074_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2430 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2430 27 27, g32p_row02_traceSegment_074_2430_0027, g32p_row02_traceSegment_074_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 2376 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2376 54 54, g32p_row02_traceSegment_074_2376_0054, g32p_row02_traceSegment_074_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2484 13 14, g32p_row02_traceSegment_074_2484_0013, g32p_row02_traceSegment_074_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2524 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2511 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2511 13 14, g32p_row02_traceSegment_074_2511_0013, g32p_row02_traceSegment_074_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2484 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2484 27 27, g32p_row02_traceSegment_074_2484_0027, g32p_row02_traceSegment_074_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2538 13 14, g32p_row02_traceSegment_074_2538_0013, g32p_row02_traceSegment_074_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2565 13 14, g32p_row02_traceSegment_074_2565_0013, g32p_row02_traceSegment_074_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2538 27 27, g32p_row02_traceSegment_074_2538_0027, g32p_row02_traceSegment_074_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 2484 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2484 54 54, g32p_row02_traceSegment_074_2484_0054, g32p_row02_traceSegment_074_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 2376 216 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2376 108 108, g32p_row02_traceSegment_074_2376_0108, g32p_row02_traceSegment_074_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_074 2160 432 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2160 216 216, g32p_row02_traceSegment_074_2160_0216, g32p_row02_traceSegment_074_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_074 1728 864 = [0, 20, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1728 432 432, g32p_row02_traceSegment_074_1728_0432, g32p_row02_traceSegment_074_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2592 13 14, g32p_row02_traceSegment_074_2592_0013, g32p_row02_traceSegment_074_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2619 13 14, g32p_row02_traceSegment_074_2619_0013, g32p_row02_traceSegment_074_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2592 27 27, g32p_row02_traceSegment_074_2592_0027, g32p_row02_traceSegment_074_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2646 13 14, g32p_row02_traceSegment_074_2646_0013, g32p_row02_traceSegment_074_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2673 13 14, g32p_row02_traceSegment_074_2673_0013, g32p_row02_traceSegment_074_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2646 27 27, g32p_row02_traceSegment_074_2646_0027, g32p_row02_traceSegment_074_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2592 54 54, g32p_row02_traceSegment_074_2592_0054, g32p_row02_traceSegment_074_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2700 13 14, g32p_row02_traceSegment_074_2700_0013, g32p_row02_traceSegment_074_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2727 13 14, g32p_row02_traceSegment_074_2727_0013, g32p_row02_traceSegment_074_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2700 27 27, g32p_row02_traceSegment_074_2700_0027, g32p_row02_traceSegment_074_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2754 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2767 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2754 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2754 13 14, g32p_row02_traceSegment_074_2754_0013, g32p_row02_traceSegment_074_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2781 13 14, g32p_row02_traceSegment_074_2781_0013, g32p_row02_traceSegment_074_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2754 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2754 27 27, g32p_row02_traceSegment_074_2754_0027, g32p_row02_traceSegment_074_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 2700 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2700 54 54, g32p_row02_traceSegment_074_2700_0054, g32p_row02_traceSegment_074_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 2592 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2592 108 108, g32p_row02_traceSegment_074_2592_0108, g32p_row02_traceSegment_074_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2808 13 14, g32p_row02_traceSegment_074_2808_0013, g32p_row02_traceSegment_074_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2835 13 14, g32p_row02_traceSegment_074_2835_0013, g32p_row02_traceSegment_074_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2808 27 27, g32p_row02_traceSegment_074_2808_0027, g32p_row02_traceSegment_074_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2862 13 14, g32p_row02_traceSegment_074_2862_0013, g32p_row02_traceSegment_074_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2902 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2889 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2889 13 14, g32p_row02_traceSegment_074_2889_0013, g32p_row02_traceSegment_074_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2862 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2862 27 27, g32p_row02_traceSegment_074_2862_0027, g32p_row02_traceSegment_074_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 2808 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2808 54 54, g32p_row02_traceSegment_074_2808_0054, g32p_row02_traceSegment_074_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2916 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2916 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2916 13 14, g32p_row02_traceSegment_074_2916_0013, g32p_row02_traceSegment_074_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2943 13 14, g32p_row02_traceSegment_074_2943_0013, g32p_row02_traceSegment_074_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2916 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2916 27 27, g32p_row02_traceSegment_074_2916_0027, g32p_row02_traceSegment_074_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2970 13 14, g32p_row02_traceSegment_074_2970_0013, g32p_row02_traceSegment_074_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2997 13 14, g32p_row02_traceSegment_074_2997_0013, g32p_row02_traceSegment_074_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2970 27 27, g32p_row02_traceSegment_074_2970_0027, g32p_row02_traceSegment_074_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 2916 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2916 54 54, g32p_row02_traceSegment_074_2916_0054, g32p_row02_traceSegment_074_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 2808 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2808 108 108, g32p_row02_traceSegment_074_2808_0108, g32p_row02_traceSegment_074_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_074 2592 432 = [0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2592 216 216, g32p_row02_traceSegment_074_2592_0216, g32p_row02_traceSegment_074_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3024 13 14, g32p_row02_traceSegment_074_3024_0013, g32p_row02_traceSegment_074_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3051 13 14, g32p_row02_traceSegment_074_3051_0013, g32p_row02_traceSegment_074_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3024 27 27, g32p_row02_traceSegment_074_3024_0027, g32p_row02_traceSegment_074_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3078 13 14, g32p_row02_traceSegment_074_3078_0013, g32p_row02_traceSegment_074_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3105 13 14, g32p_row02_traceSegment_074_3105_0013, g32p_row02_traceSegment_074_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3078 27 27, g32p_row02_traceSegment_074_3078_0027, g32p_row02_traceSegment_074_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3024 54 54, g32p_row02_traceSegment_074_3024_0054, g32p_row02_traceSegment_074_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3145 14 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3132 27 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3132 13 14, g32p_row02_traceSegment_074_3132_0013, g32p_row02_traceSegment_074_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3172 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3159 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3159 13 14, g32p_row02_traceSegment_074_3159_0013, g32p_row02_traceSegment_074_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 3132 54 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3132 27 27, g32p_row02_traceSegment_074_3132_0027, g32p_row02_traceSegment_074_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3186 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3186 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3186 13 14, g32p_row02_traceSegment_074_3186_0013, g32p_row02_traceSegment_074_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3213 13 14, g32p_row02_traceSegment_074_3213_0013, g32p_row02_traceSegment_074_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 3186 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3186 27 27, g32p_row02_traceSegment_074_3186_0027, g32p_row02_traceSegment_074_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 3132 108 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3132 54 54, g32p_row02_traceSegment_074_3132_0054, g32p_row02_traceSegment_074_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 3024 216 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3024 108 108, g32p_row02_traceSegment_074_3024_0108, g32p_row02_traceSegment_074_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3240 13 14, g32p_row02_traceSegment_074_3240_0013, g32p_row02_traceSegment_074_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3267 13 14, g32p_row02_traceSegment_074_3267_0013, g32p_row02_traceSegment_074_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3240 27 27, g32p_row02_traceSegment_074_3240_0027, g32p_row02_traceSegment_074_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3294 13 14, g32p_row02_traceSegment_074_3294_0013, g32p_row02_traceSegment_074_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3321 13 14, g32p_row02_traceSegment_074_3321_0013, g32p_row02_traceSegment_074_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3294 27 27, g32p_row02_traceSegment_074_3294_0027, g32p_row02_traceSegment_074_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3240 54 54, g32p_row02_traceSegment_074_3240_0054, g32p_row02_traceSegment_074_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3348 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3348 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3348 13 14, g32p_row02_traceSegment_074_3348_0013, g32p_row02_traceSegment_074_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3375 13 14, g32p_row02_traceSegment_074_3375_0013, g32p_row02_traceSegment_074_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 3348 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3348 27 27, g32p_row02_traceSegment_074_3348_0027, g32p_row02_traceSegment_074_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3402 13 14, g32p_row02_traceSegment_074_3402_0013, g32p_row02_traceSegment_074_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_074 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_074 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_074_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_074 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3429 13 14, g32p_row02_traceSegment_074_3429_0013, g32p_row02_traceSegment_074_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_074 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3402 27 27, g32p_row02_traceSegment_074_3402_0027, g32p_row02_traceSegment_074_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_074 3348 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3348 54 54, g32p_row02_traceSegment_074_3348_0054, g32p_row02_traceSegment_074_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_074 3240 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3240 108 108, g32p_row02_traceSegment_074_3240_0108, g32p_row02_traceSegment_074_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_074_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_074 3024 432 = [0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 3024 216 216, g32p_row02_traceSegment_074_3024_0216, g32p_row02_traceSegment_074_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_074_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_074 2592 864 = [0, 6, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 2592 432 432, g32p_row02_traceSegment_074_2592_0432, g32p_row02_traceSegment_074_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_074_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_074 1728 1728 = [0, 26, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 1728 864 864, g32p_row02_traceSegment_074_1728_0864, g32p_row02_traceSegment_074_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_074_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_074 0 3456 = [0, 96, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_074 0 1728 1728, g32p_row02_traceSegment_074_0000_1728, g32p_row02_traceSegment_074_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 74 = [0, 96, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_074_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_075 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 75 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_075_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 0 13 14, g32p_row02_traceSegment_075_0000_0013, g32p_row02_traceSegment_075_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 27 13 14, g32p_row02_traceSegment_075_0027_0013, g32p_row02_traceSegment_075_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 0 27 27, g32p_row02_traceSegment_075_0000_0027, g32p_row02_traceSegment_075_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 54 13 14, g32p_row02_traceSegment_075_0054_0013, g32p_row02_traceSegment_075_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 81 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 81 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 81 13 14, g32p_row02_traceSegment_075_0081_0013, g32p_row02_traceSegment_075_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 54 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 54 27 27, g32p_row02_traceSegment_075_0054_0027, g32p_row02_traceSegment_075_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 0 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 0 54 54, g32p_row02_traceSegment_075_0000_0054, g32p_row02_traceSegment_075_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 108 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 108 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 108 13 14, g32p_row02_traceSegment_075_0108_0013, g32p_row02_traceSegment_075_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 135 13 14, g32p_row02_traceSegment_075_0135_0013, g32p_row02_traceSegment_075_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 108 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 108 27 27, g32p_row02_traceSegment_075_0108_0027, g32p_row02_traceSegment_075_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 162 13 14, g32p_row02_traceSegment_075_0162_0013, g32p_row02_traceSegment_075_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 189 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 202 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 189 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 189 13 14, g32p_row02_traceSegment_075_0189_0013, g32p_row02_traceSegment_075_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 162 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 162 27 27, g32p_row02_traceSegment_075_0162_0027, g32p_row02_traceSegment_075_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 108 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 108 54 54, g32p_row02_traceSegment_075_0108_0054, g32p_row02_traceSegment_075_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 0 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 0 108 108, g32p_row02_traceSegment_075_0000_0108, g32p_row02_traceSegment_075_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 216 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 229 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 216 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 216 13 14, g32p_row02_traceSegment_075_0216_0013, g32p_row02_traceSegment_075_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 243 13 14, g32p_row02_traceSegment_075_0243_0013, g32p_row02_traceSegment_075_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 216 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 216 27 27, g32p_row02_traceSegment_075_0216_0027, g32p_row02_traceSegment_075_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 270 13 14, g32p_row02_traceSegment_075_0270_0013, g32p_row02_traceSegment_075_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 297 13 14, g32p_row02_traceSegment_075_0297_0013, g32p_row02_traceSegment_075_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 270 27 27, g32p_row02_traceSegment_075_0270_0027, g32p_row02_traceSegment_075_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 216 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 216 54 54, g32p_row02_traceSegment_075_0216_0054, g32p_row02_traceSegment_075_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 324 13 14, g32p_row02_traceSegment_075_0324_0013, g32p_row02_traceSegment_075_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 351 13 14, g32p_row02_traceSegment_075_0351_0013, g32p_row02_traceSegment_075_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 324 27 27, g32p_row02_traceSegment_075_0324_0027, g32p_row02_traceSegment_075_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 378 13 14, g32p_row02_traceSegment_075_0378_0013, g32p_row02_traceSegment_075_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 405 13 14, g32p_row02_traceSegment_075_0405_0013, g32p_row02_traceSegment_075_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 378 27 27, g32p_row02_traceSegment_075_0378_0027, g32p_row02_traceSegment_075_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 324 54 54, g32p_row02_traceSegment_075_0324_0054, g32p_row02_traceSegment_075_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 216 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 216 108 108, g32p_row02_traceSegment_075_0216_0108, g32p_row02_traceSegment_075_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_075 0 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 0 216 216, g32p_row02_traceSegment_075_0000_0216, g32p_row02_traceSegment_075_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 432 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 432 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 432 13 14, g32p_row02_traceSegment_075_0432_0013, g32p_row02_traceSegment_075_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 459 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 459 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 459 13 14, g32p_row02_traceSegment_075_0459_0013, g32p_row02_traceSegment_075_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 432 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 432 27 27, g32p_row02_traceSegment_075_0432_0027, g32p_row02_traceSegment_075_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 486 13 14, g32p_row02_traceSegment_075_0486_0013, g32p_row02_traceSegment_075_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 513 13 14, g32p_row02_traceSegment_075_0513_0013, g32p_row02_traceSegment_075_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 486 27 27, g32p_row02_traceSegment_075_0486_0027, g32p_row02_traceSegment_075_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 432 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 432 54 54, g32p_row02_traceSegment_075_0432_0054, g32p_row02_traceSegment_075_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 540 13 14, g32p_row02_traceSegment_075_0540_0013, g32p_row02_traceSegment_075_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 567 13 14, g32p_row02_traceSegment_075_0567_0013, g32p_row02_traceSegment_075_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 540 27 27, g32p_row02_traceSegment_075_0540_0027, g32p_row02_traceSegment_075_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 594 13 14, g32p_row02_traceSegment_075_0594_0013, g32p_row02_traceSegment_075_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 621 13 14, g32p_row02_traceSegment_075_0621_0013, g32p_row02_traceSegment_075_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 594 27 27, g32p_row02_traceSegment_075_0594_0027, g32p_row02_traceSegment_075_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 540 54 54, g32p_row02_traceSegment_075_0540_0054, g32p_row02_traceSegment_075_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 432 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 432 108 108, g32p_row02_traceSegment_075_0432_0108, g32p_row02_traceSegment_075_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 648 13 14, g32p_row02_traceSegment_075_0648_0013, g32p_row02_traceSegment_075_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 675 13 14, g32p_row02_traceSegment_075_0675_0013, g32p_row02_traceSegment_075_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 648 27 27, g32p_row02_traceSegment_075_0648_0027, g32p_row02_traceSegment_075_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 702 13 14, g32p_row02_traceSegment_075_0702_0013, g32p_row02_traceSegment_075_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 729 13 14, g32p_row02_traceSegment_075_0729_0013, g32p_row02_traceSegment_075_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 702 27 27, g32p_row02_traceSegment_075_0702_0027, g32p_row02_traceSegment_075_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 648 54 54, g32p_row02_traceSegment_075_0648_0054, g32p_row02_traceSegment_075_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 756 13 14, g32p_row02_traceSegment_075_0756_0013, g32p_row02_traceSegment_075_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 783 13 14, g32p_row02_traceSegment_075_0783_0013, g32p_row02_traceSegment_075_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 756 27 27, g32p_row02_traceSegment_075_0756_0027, g32p_row02_traceSegment_075_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 810 13 14, g32p_row02_traceSegment_075_0810_0013, g32p_row02_traceSegment_075_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 837 13 14, g32p_row02_traceSegment_075_0837_0013, g32p_row02_traceSegment_075_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 810 27 27, g32p_row02_traceSegment_075_0810_0027, g32p_row02_traceSegment_075_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 756 54 54, g32p_row02_traceSegment_075_0756_0054, g32p_row02_traceSegment_075_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 648 108 108, g32p_row02_traceSegment_075_0648_0108, g32p_row02_traceSegment_075_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_075 432 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 432 216 216, g32p_row02_traceSegment_075_0432_0216, g32p_row02_traceSegment_075_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_075 0 864 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 0 432 432, g32p_row02_traceSegment_075_0000_0432, g32p_row02_traceSegment_075_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 864 13 14, g32p_row02_traceSegment_075_0864_0013, g32p_row02_traceSegment_075_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 891 13 14, g32p_row02_traceSegment_075_0891_0013, g32p_row02_traceSegment_075_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 864 27 27, g32p_row02_traceSegment_075_0864_0027, g32p_row02_traceSegment_075_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 918 13 14, g32p_row02_traceSegment_075_0918_0013, g32p_row02_traceSegment_075_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 945 13 14, g32p_row02_traceSegment_075_0945_0013, g32p_row02_traceSegment_075_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 918 27 27, g32p_row02_traceSegment_075_0918_0027, g32p_row02_traceSegment_075_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 864 54 54, g32p_row02_traceSegment_075_0864_0054, g32p_row02_traceSegment_075_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 972 13 14, g32p_row02_traceSegment_075_0972_0013, g32p_row02_traceSegment_075_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 999 13 14, g32p_row02_traceSegment_075_0999_0013, g32p_row02_traceSegment_075_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 972 27 27, g32p_row02_traceSegment_075_0972_0027, g32p_row02_traceSegment_075_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1026 13 14, g32p_row02_traceSegment_075_1026_0013, g32p_row02_traceSegment_075_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1053 13 14, g32p_row02_traceSegment_075_1053_0013, g32p_row02_traceSegment_075_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1026 27 27, g32p_row02_traceSegment_075_1026_0027, g32p_row02_traceSegment_075_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 972 54 54, g32p_row02_traceSegment_075_0972_0054, g32p_row02_traceSegment_075_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 864 108 108, g32p_row02_traceSegment_075_0864_0108, g32p_row02_traceSegment_075_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1080 13 14, g32p_row02_traceSegment_075_1080_0013, g32p_row02_traceSegment_075_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1107 13 14, g32p_row02_traceSegment_075_1107_0013, g32p_row02_traceSegment_075_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1080 27 27, g32p_row02_traceSegment_075_1080_0027, g32p_row02_traceSegment_075_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1134 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1147 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1134 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1134 13 14, g32p_row02_traceSegment_075_1134_0013, g32p_row02_traceSegment_075_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1161 13 14, g32p_row02_traceSegment_075_1161_0013, g32p_row02_traceSegment_075_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1134 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1134 27 27, g32p_row02_traceSegment_075_1134_0027, g32p_row02_traceSegment_075_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 1080 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1080 54 54, g32p_row02_traceSegment_075_1080_0054, g32p_row02_traceSegment_075_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1188 13 14, g32p_row02_traceSegment_075_1188_0013, g32p_row02_traceSegment_075_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1215 13 14, g32p_row02_traceSegment_075_1215_0013, g32p_row02_traceSegment_075_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1188 27 27, g32p_row02_traceSegment_075_1188_0027, g32p_row02_traceSegment_075_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1242 13 14, g32p_row02_traceSegment_075_1242_0013, g32p_row02_traceSegment_075_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1269 13 14, g32p_row02_traceSegment_075_1269_0013, g32p_row02_traceSegment_075_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1242 27 27, g32p_row02_traceSegment_075_1242_0027, g32p_row02_traceSegment_075_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1188 54 54, g32p_row02_traceSegment_075_1188_0054, g32p_row02_traceSegment_075_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 1080 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1080 108 108, g32p_row02_traceSegment_075_1080_0108, g32p_row02_traceSegment_075_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_075 864 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 864 216 216, g32p_row02_traceSegment_075_0864_0216, g32p_row02_traceSegment_075_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1296 13 14, g32p_row02_traceSegment_075_1296_0013, g32p_row02_traceSegment_075_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1323 13 14, g32p_row02_traceSegment_075_1323_0013, g32p_row02_traceSegment_075_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1296 27 27, g32p_row02_traceSegment_075_1296_0027, g32p_row02_traceSegment_075_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1350 13 14, g32p_row02_traceSegment_075_1350_0013, g32p_row02_traceSegment_075_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1377 13 14, g32p_row02_traceSegment_075_1377_0013, g32p_row02_traceSegment_075_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1350 27 27, g32p_row02_traceSegment_075_1350_0027, g32p_row02_traceSegment_075_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1296 54 54, g32p_row02_traceSegment_075_1296_0054, g32p_row02_traceSegment_075_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1404 13 14, g32p_row02_traceSegment_075_1404_0013, g32p_row02_traceSegment_075_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1431 13 14, g32p_row02_traceSegment_075_1431_0013, g32p_row02_traceSegment_075_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1404 27 27, g32p_row02_traceSegment_075_1404_0027, g32p_row02_traceSegment_075_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1458 13 14, g32p_row02_traceSegment_075_1458_0013, g32p_row02_traceSegment_075_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1485 13 14, g32p_row02_traceSegment_075_1485_0013, g32p_row02_traceSegment_075_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1458 27 27, g32p_row02_traceSegment_075_1458_0027, g32p_row02_traceSegment_075_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1404 54 54, g32p_row02_traceSegment_075_1404_0054, g32p_row02_traceSegment_075_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1296 108 108, g32p_row02_traceSegment_075_1296_0108, g32p_row02_traceSegment_075_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1512 13 14, g32p_row02_traceSegment_075_1512_0013, g32p_row02_traceSegment_075_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1539 13 14, g32p_row02_traceSegment_075_1539_0013, g32p_row02_traceSegment_075_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1512 27 27, g32p_row02_traceSegment_075_1512_0027, g32p_row02_traceSegment_075_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1566 13 14, g32p_row02_traceSegment_075_1566_0013, g32p_row02_traceSegment_075_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1593 13 14, g32p_row02_traceSegment_075_1593_0013, g32p_row02_traceSegment_075_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1566 27 27, g32p_row02_traceSegment_075_1566_0027, g32p_row02_traceSegment_075_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1512 54 54, g32p_row02_traceSegment_075_1512_0054, g32p_row02_traceSegment_075_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1620 13 14, g32p_row02_traceSegment_075_1620_0013, g32p_row02_traceSegment_075_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1647 13 14, g32p_row02_traceSegment_075_1647_0013, g32p_row02_traceSegment_075_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1620 27 27, g32p_row02_traceSegment_075_1620_0027, g32p_row02_traceSegment_075_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1674 13 14, g32p_row02_traceSegment_075_1674_0013, g32p_row02_traceSegment_075_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1701 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1714 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1701 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1701 13 14, g32p_row02_traceSegment_075_1701_0013, g32p_row02_traceSegment_075_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1674 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1674 27 27, g32p_row02_traceSegment_075_1674_0027, g32p_row02_traceSegment_075_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 1620 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1620 54 54, g32p_row02_traceSegment_075_1620_0054, g32p_row02_traceSegment_075_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 1512 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1512 108 108, g32p_row02_traceSegment_075_1512_0108, g32p_row02_traceSegment_075_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_075 1296 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1296 216 216, g32p_row02_traceSegment_075_1296_0216, g32p_row02_traceSegment_075_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_075 864 864 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 864 432 432, g32p_row02_traceSegment_075_0864_0432, g32p_row02_traceSegment_075_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_075 0 1728 = [14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 0 864 864, g32p_row02_traceSegment_075_0000_0864, g32p_row02_traceSegment_075_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1728 13 14, g32p_row02_traceSegment_075_1728_0013, g32p_row02_traceSegment_075_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1755 13 14, g32p_row02_traceSegment_075_1755_0013, g32p_row02_traceSegment_075_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1728 27 27, g32p_row02_traceSegment_075_1728_0027, g32p_row02_traceSegment_075_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1782 13 14, g32p_row02_traceSegment_075_1782_0013, g32p_row02_traceSegment_075_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1809 13 14, g32p_row02_traceSegment_075_1809_0013, g32p_row02_traceSegment_075_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1782 27 27, g32p_row02_traceSegment_075_1782_0027, g32p_row02_traceSegment_075_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1728 54 54, g32p_row02_traceSegment_075_1728_0054, g32p_row02_traceSegment_075_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1836 13 14, g32p_row02_traceSegment_075_1836_0013, g32p_row02_traceSegment_075_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1863 13 14, g32p_row02_traceSegment_075_1863_0013, g32p_row02_traceSegment_075_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1836 27 27, g32p_row02_traceSegment_075_1836_0027, g32p_row02_traceSegment_075_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1890 13 14, g32p_row02_traceSegment_075_1890_0013, g32p_row02_traceSegment_075_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1917 13 14, g32p_row02_traceSegment_075_1917_0013, g32p_row02_traceSegment_075_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1890 27 27, g32p_row02_traceSegment_075_1890_0027, g32p_row02_traceSegment_075_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1836 54 54, g32p_row02_traceSegment_075_1836_0054, g32p_row02_traceSegment_075_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1728 108 108, g32p_row02_traceSegment_075_1728_0108, g32p_row02_traceSegment_075_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1944 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1957 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1944 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1944 13 14, g32p_row02_traceSegment_075_1944_0013, g32p_row02_traceSegment_075_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1971 13 14, g32p_row02_traceSegment_075_1971_0013, g32p_row02_traceSegment_075_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1944 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1944 27 27, g32p_row02_traceSegment_075_1944_0027, g32p_row02_traceSegment_075_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2011 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 1998 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1998 13 14, g32p_row02_traceSegment_075_1998_0013, g32p_row02_traceSegment_075_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2025 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2038 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2025 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2025 13 14, g32p_row02_traceSegment_075_2025_0013, g32p_row02_traceSegment_075_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 1998 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1998 27 27, g32p_row02_traceSegment_075_1998_0027, g32p_row02_traceSegment_075_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 1944 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1944 54 54, g32p_row02_traceSegment_075_1944_0054, g32p_row02_traceSegment_075_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2052 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2052 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2052 13 14, g32p_row02_traceSegment_075_2052_0013, g32p_row02_traceSegment_075_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2079 13 14, g32p_row02_traceSegment_075_2079_0013, g32p_row02_traceSegment_075_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2052 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2052 27 27, g32p_row02_traceSegment_075_2052_0027, g32p_row02_traceSegment_075_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2119 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2106 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2106 13 14, g32p_row02_traceSegment_075_2106_0013, g32p_row02_traceSegment_075_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2133 13 14, g32p_row02_traceSegment_075_2133_0013, g32p_row02_traceSegment_075_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2106 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2106 27 27, g32p_row02_traceSegment_075_2106_0027, g32p_row02_traceSegment_075_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 2052 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2052 54 54, g32p_row02_traceSegment_075_2052_0054, g32p_row02_traceSegment_075_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 1944 216 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1944 108 108, g32p_row02_traceSegment_075_1944_0108, g32p_row02_traceSegment_075_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_075 1728 432 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1728 216 216, g32p_row02_traceSegment_075_1728_0216, g32p_row02_traceSegment_075_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2160 13 14, g32p_row02_traceSegment_075_2160_0013, g32p_row02_traceSegment_075_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2187 13 14, g32p_row02_traceSegment_075_2187_0013, g32p_row02_traceSegment_075_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2160 27 27, g32p_row02_traceSegment_075_2160_0027, g32p_row02_traceSegment_075_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2214 13 14, g32p_row02_traceSegment_075_2214_0013, g32p_row02_traceSegment_075_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2241 13 14, g32p_row02_traceSegment_075_2241_0013, g32p_row02_traceSegment_075_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2214 27 27, g32p_row02_traceSegment_075_2214_0027, g32p_row02_traceSegment_075_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2160 54 54, g32p_row02_traceSegment_075_2160_0054, g32p_row02_traceSegment_075_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2268 13 14, g32p_row02_traceSegment_075_2268_0013, g32p_row02_traceSegment_075_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2295 13 14, g32p_row02_traceSegment_075_2295_0013, g32p_row02_traceSegment_075_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2268 27 27, g32p_row02_traceSegment_075_2268_0027, g32p_row02_traceSegment_075_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2322 13 14, g32p_row02_traceSegment_075_2322_0013, g32p_row02_traceSegment_075_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2349 13 14, g32p_row02_traceSegment_075_2349_0013, g32p_row02_traceSegment_075_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2322 27 27, g32p_row02_traceSegment_075_2322_0027, g32p_row02_traceSegment_075_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2268 54 54, g32p_row02_traceSegment_075_2268_0054, g32p_row02_traceSegment_075_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2160 108 108, g32p_row02_traceSegment_075_2160_0108, g32p_row02_traceSegment_075_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2376 13 14, g32p_row02_traceSegment_075_2376_0013, g32p_row02_traceSegment_075_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2403 13 14, g32p_row02_traceSegment_075_2403_0013, g32p_row02_traceSegment_075_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2376 27 27, g32p_row02_traceSegment_075_2376_0027, g32p_row02_traceSegment_075_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2430 13 14, g32p_row02_traceSegment_075_2430_0013, g32p_row02_traceSegment_075_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2457 13 14, g32p_row02_traceSegment_075_2457_0013, g32p_row02_traceSegment_075_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2430 27 27, g32p_row02_traceSegment_075_2430_0027, g32p_row02_traceSegment_075_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2376 54 54, g32p_row02_traceSegment_075_2376_0054, g32p_row02_traceSegment_075_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2484 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2497 14 = [3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2484 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2484 13 14, g32p_row02_traceSegment_075_2484_0013, g32p_row02_traceSegment_075_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2511 13 14, g32p_row02_traceSegment_075_2511_0013, g32p_row02_traceSegment_075_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2484 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2484 27 27, g32p_row02_traceSegment_075_2484_0027, g32p_row02_traceSegment_075_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2538 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2551 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2538 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2538 13 14, g32p_row02_traceSegment_075_2538_0013, g32p_row02_traceSegment_075_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2565 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2565 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2565 13 14, g32p_row02_traceSegment_075_2565_0013, g32p_row02_traceSegment_075_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2538 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2538 27 27, g32p_row02_traceSegment_075_2538_0027, g32p_row02_traceSegment_075_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 2484 108 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2484 54 54, g32p_row02_traceSegment_075_2484_0054, g32p_row02_traceSegment_075_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 2376 216 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2376 108 108, g32p_row02_traceSegment_075_2376_0108, g32p_row02_traceSegment_075_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_075 2160 432 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2160 216 216, g32p_row02_traceSegment_075_2160_0216, g32p_row02_traceSegment_075_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_075 1728 864 = [16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1728 432 432, g32p_row02_traceSegment_075_1728_0432, g32p_row02_traceSegment_075_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2592 13 14, g32p_row02_traceSegment_075_2592_0013, g32p_row02_traceSegment_075_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2619 13 14, g32p_row02_traceSegment_075_2619_0013, g32p_row02_traceSegment_075_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2592 27 27, g32p_row02_traceSegment_075_2592_0027, g32p_row02_traceSegment_075_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2646 13 14, g32p_row02_traceSegment_075_2646_0013, g32p_row02_traceSegment_075_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2673 13 14, g32p_row02_traceSegment_075_2673_0013, g32p_row02_traceSegment_075_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2646 27 27, g32p_row02_traceSegment_075_2646_0027, g32p_row02_traceSegment_075_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2592 54 54, g32p_row02_traceSegment_075_2592_0054, g32p_row02_traceSegment_075_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2700 13 14, g32p_row02_traceSegment_075_2700_0013, g32p_row02_traceSegment_075_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2727 13 14, g32p_row02_traceSegment_075_2727_0013, g32p_row02_traceSegment_075_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2700 27 27, g32p_row02_traceSegment_075_2700_0027, g32p_row02_traceSegment_075_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2767 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2754 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2754 13 14, g32p_row02_traceSegment_075_2754_0013, g32p_row02_traceSegment_075_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2781 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2781 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2781 13 14, g32p_row02_traceSegment_075_2781_0013, g32p_row02_traceSegment_075_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2754 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2754 27 27, g32p_row02_traceSegment_075_2754_0027, g32p_row02_traceSegment_075_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 2700 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2700 54 54, g32p_row02_traceSegment_075_2700_0054, g32p_row02_traceSegment_075_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 2592 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2592 108 108, g32p_row02_traceSegment_075_2592_0108, g32p_row02_traceSegment_075_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2808 13 14, g32p_row02_traceSegment_075_2808_0013, g32p_row02_traceSegment_075_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2835 13 14, g32p_row02_traceSegment_075_2835_0013, g32p_row02_traceSegment_075_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2808 27 27, g32p_row02_traceSegment_075_2808_0027, g32p_row02_traceSegment_075_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2862 13 14, g32p_row02_traceSegment_075_2862_0013, g32p_row02_traceSegment_075_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2889 13 14, g32p_row02_traceSegment_075_2889_0013, g32p_row02_traceSegment_075_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2862 27 27, g32p_row02_traceSegment_075_2862_0027, g32p_row02_traceSegment_075_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2808 54 54, g32p_row02_traceSegment_075_2808_0054, g32p_row02_traceSegment_075_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2916 13 14, g32p_row02_traceSegment_075_2916_0013, g32p_row02_traceSegment_075_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2943 13 14, g32p_row02_traceSegment_075_2943_0013, g32p_row02_traceSegment_075_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2916 27 27, g32p_row02_traceSegment_075_2916_0027, g32p_row02_traceSegment_075_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2970 13 14, g32p_row02_traceSegment_075_2970_0013, g32p_row02_traceSegment_075_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2997 13 14, g32p_row02_traceSegment_075_2997_0013, g32p_row02_traceSegment_075_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2970 27 27, g32p_row02_traceSegment_075_2970_0027, g32p_row02_traceSegment_075_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2916 54 54, g32p_row02_traceSegment_075_2916_0054, g32p_row02_traceSegment_075_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2808 108 108, g32p_row02_traceSegment_075_2808_0108, g32p_row02_traceSegment_075_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_075 2592 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2592 216 216, g32p_row02_traceSegment_075_2592_0216, g32p_row02_traceSegment_075_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3024 13 14, g32p_row02_traceSegment_075_3024_0013, g32p_row02_traceSegment_075_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3051 13 14, g32p_row02_traceSegment_075_3051_0013, g32p_row02_traceSegment_075_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3024 27 27, g32p_row02_traceSegment_075_3024_0027, g32p_row02_traceSegment_075_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3078 13 14, g32p_row02_traceSegment_075_3078_0013, g32p_row02_traceSegment_075_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3105 13 14, g32p_row02_traceSegment_075_3105_0013, g32p_row02_traceSegment_075_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3078 27 27, g32p_row02_traceSegment_075_3078_0027, g32p_row02_traceSegment_075_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3024 54 54, g32p_row02_traceSegment_075_3024_0054, g32p_row02_traceSegment_075_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3132 13 14, g32p_row02_traceSegment_075_3132_0013, g32p_row02_traceSegment_075_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3159 13 14, g32p_row02_traceSegment_075_3159_0013, g32p_row02_traceSegment_075_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3132 27 27, g32p_row02_traceSegment_075_3132_0027, g32p_row02_traceSegment_075_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3186 13 14, g32p_row02_traceSegment_075_3186_0013, g32p_row02_traceSegment_075_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3213 13 14, g32p_row02_traceSegment_075_3213_0013, g32p_row02_traceSegment_075_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3186 27 27, g32p_row02_traceSegment_075_3186_0027, g32p_row02_traceSegment_075_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3132 54 54, g32p_row02_traceSegment_075_3132_0054, g32p_row02_traceSegment_075_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3024 108 108, g32p_row02_traceSegment_075_3024_0108, g32p_row02_traceSegment_075_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3240 13 14, g32p_row02_traceSegment_075_3240_0013, g32p_row02_traceSegment_075_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3267 13 14, g32p_row02_traceSegment_075_3267_0013, g32p_row02_traceSegment_075_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3240 27 27, g32p_row02_traceSegment_075_3240_0027, g32p_row02_traceSegment_075_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3294 13 14, g32p_row02_traceSegment_075_3294_0013, g32p_row02_traceSegment_075_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3321 13 14, g32p_row02_traceSegment_075_3321_0013, g32p_row02_traceSegment_075_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3294 27 27, g32p_row02_traceSegment_075_3294_0027, g32p_row02_traceSegment_075_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3240 54 54, g32p_row02_traceSegment_075_3240_0054, g32p_row02_traceSegment_075_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3348 13 14, g32p_row02_traceSegment_075_3348_0013, g32p_row02_traceSegment_075_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3375 13 14, g32p_row02_traceSegment_075_3375_0013, g32p_row02_traceSegment_075_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3348 27 27, g32p_row02_traceSegment_075_3348_0027, g32p_row02_traceSegment_075_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3402 13 14, g32p_row02_traceSegment_075_3402_0013, g32p_row02_traceSegment_075_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_075 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_075 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_075_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_075 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3429 13 14, g32p_row02_traceSegment_075_3429_0013, g32p_row02_traceSegment_075_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_075 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3402 27 27, g32p_row02_traceSegment_075_3402_0027, g32p_row02_traceSegment_075_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_075 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3348 54 54, g32p_row02_traceSegment_075_3348_0054, g32p_row02_traceSegment_075_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_075 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3240 108 108, g32p_row02_traceSegment_075_3240_0108, g32p_row02_traceSegment_075_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_075_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_075 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 3024 216 216, g32p_row02_traceSegment_075_3024_0216, g32p_row02_traceSegment_075_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_075_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_075 2592 864 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 2592 432 432, g32p_row02_traceSegment_075_2592_0432, g32p_row02_traceSegment_075_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_075_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_075 1728 1728 = [18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 1728 864 864, g32p_row02_traceSegment_075_1728_0864, g32p_row02_traceSegment_075_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_075_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_075 0 3456 = [32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_075 0 1728 1728, g32p_row02_traceSegment_075_0000_1728, g32p_row02_traceSegment_075_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 75 = [32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_075_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_076 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 76 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_076_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 0 13 14, g32p_row02_traceSegment_076_0000_0013, g32p_row02_traceSegment_076_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 27 13 14, g32p_row02_traceSegment_076_0027_0013, g32p_row02_traceSegment_076_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 0 27 27, g32p_row02_traceSegment_076_0000_0027, g32p_row02_traceSegment_076_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 54 13 14, g32p_row02_traceSegment_076_0054_0013, g32p_row02_traceSegment_076_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 81 13 14, g32p_row02_traceSegment_076_0081_0013, g32p_row02_traceSegment_076_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 54 27 27, g32p_row02_traceSegment_076_0054_0027, g32p_row02_traceSegment_076_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 0 54 54, g32p_row02_traceSegment_076_0000_0054, g32p_row02_traceSegment_076_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 121 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 108 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 108 13 14, g32p_row02_traceSegment_076_0108_0013, g32p_row02_traceSegment_076_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 148 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 135 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 135 13 14, g32p_row02_traceSegment_076_0135_0013, g32p_row02_traceSegment_076_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 108 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 108 27 27, g32p_row02_traceSegment_076_0108_0027, g32p_row02_traceSegment_076_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 162 13 14, g32p_row02_traceSegment_076_0162_0013, g32p_row02_traceSegment_076_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 189 13 14, g32p_row02_traceSegment_076_0189_0013, g32p_row02_traceSegment_076_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 162 27 27, g32p_row02_traceSegment_076_0162_0027, g32p_row02_traceSegment_076_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 108 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 108 54 54, g32p_row02_traceSegment_076_0108_0054, g32p_row02_traceSegment_076_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 0 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 0 108 108, g32p_row02_traceSegment_076_0000_0108, g32p_row02_traceSegment_076_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 216 13 14, g32p_row02_traceSegment_076_0216_0013, g32p_row02_traceSegment_076_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 243 13 14, g32p_row02_traceSegment_076_0243_0013, g32p_row02_traceSegment_076_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 216 27 27, g32p_row02_traceSegment_076_0216_0027, g32p_row02_traceSegment_076_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 270 13 14, g32p_row02_traceSegment_076_0270_0013, g32p_row02_traceSegment_076_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 297 13 14, g32p_row02_traceSegment_076_0297_0013, g32p_row02_traceSegment_076_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 270 27 27, g32p_row02_traceSegment_076_0270_0027, g32p_row02_traceSegment_076_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 216 54 54, g32p_row02_traceSegment_076_0216_0054, g32p_row02_traceSegment_076_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 324 13 14, g32p_row02_traceSegment_076_0324_0013, g32p_row02_traceSegment_076_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 351 13 14, g32p_row02_traceSegment_076_0351_0013, g32p_row02_traceSegment_076_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 324 27 27, g32p_row02_traceSegment_076_0324_0027, g32p_row02_traceSegment_076_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 378 13 14, g32p_row02_traceSegment_076_0378_0013, g32p_row02_traceSegment_076_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 405 13 14, g32p_row02_traceSegment_076_0405_0013, g32p_row02_traceSegment_076_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 378 27 27, g32p_row02_traceSegment_076_0378_0027, g32p_row02_traceSegment_076_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 324 54 54, g32p_row02_traceSegment_076_0324_0054, g32p_row02_traceSegment_076_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 216 108 108, g32p_row02_traceSegment_076_0216_0108, g32p_row02_traceSegment_076_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_076 0 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 0 216 216, g32p_row02_traceSegment_076_0000_0216, g32p_row02_traceSegment_076_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 432 13 14, g32p_row02_traceSegment_076_0432_0013, g32p_row02_traceSegment_076_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 459 13 14, g32p_row02_traceSegment_076_0459_0013, g32p_row02_traceSegment_076_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 432 27 27, g32p_row02_traceSegment_076_0432_0027, g32p_row02_traceSegment_076_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 486 13 14, g32p_row02_traceSegment_076_0486_0013, g32p_row02_traceSegment_076_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 513 13 14, g32p_row02_traceSegment_076_0513_0013, g32p_row02_traceSegment_076_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 486 27 27, g32p_row02_traceSegment_076_0486_0027, g32p_row02_traceSegment_076_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 432 54 54, g32p_row02_traceSegment_076_0432_0054, g32p_row02_traceSegment_076_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 540 13 14, g32p_row02_traceSegment_076_0540_0013, g32p_row02_traceSegment_076_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 567 13 14, g32p_row02_traceSegment_076_0567_0013, g32p_row02_traceSegment_076_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 540 27 27, g32p_row02_traceSegment_076_0540_0027, g32p_row02_traceSegment_076_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 594 13 14, g32p_row02_traceSegment_076_0594_0013, g32p_row02_traceSegment_076_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 621 13 14, g32p_row02_traceSegment_076_0621_0013, g32p_row02_traceSegment_076_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 594 27 27, g32p_row02_traceSegment_076_0594_0027, g32p_row02_traceSegment_076_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 540 54 54, g32p_row02_traceSegment_076_0540_0054, g32p_row02_traceSegment_076_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 432 108 108, g32p_row02_traceSegment_076_0432_0108, g32p_row02_traceSegment_076_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 648 13 14, g32p_row02_traceSegment_076_0648_0013, g32p_row02_traceSegment_076_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 675 13 14, g32p_row02_traceSegment_076_0675_0013, g32p_row02_traceSegment_076_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 648 27 27, g32p_row02_traceSegment_076_0648_0027, g32p_row02_traceSegment_076_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 702 13 14, g32p_row02_traceSegment_076_0702_0013, g32p_row02_traceSegment_076_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 729 13 14, g32p_row02_traceSegment_076_0729_0013, g32p_row02_traceSegment_076_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 702 27 27, g32p_row02_traceSegment_076_0702_0027, g32p_row02_traceSegment_076_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 648 54 54, g32p_row02_traceSegment_076_0648_0054, g32p_row02_traceSegment_076_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 756 13 14, g32p_row02_traceSegment_076_0756_0013, g32p_row02_traceSegment_076_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 783 13 14, g32p_row02_traceSegment_076_0783_0013, g32p_row02_traceSegment_076_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 756 27 27, g32p_row02_traceSegment_076_0756_0027, g32p_row02_traceSegment_076_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 810 13 14, g32p_row02_traceSegment_076_0810_0013, g32p_row02_traceSegment_076_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 837 13 14, g32p_row02_traceSegment_076_0837_0013, g32p_row02_traceSegment_076_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 810 27 27, g32p_row02_traceSegment_076_0810_0027, g32p_row02_traceSegment_076_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 756 54 54, g32p_row02_traceSegment_076_0756_0054, g32p_row02_traceSegment_076_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 648 108 108, g32p_row02_traceSegment_076_0648_0108, g32p_row02_traceSegment_076_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_076 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 432 216 216, g32p_row02_traceSegment_076_0432_0216, g32p_row02_traceSegment_076_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_076 0 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 0 432 432, g32p_row02_traceSegment_076_0000_0432, g32p_row02_traceSegment_076_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 864 13 14, g32p_row02_traceSegment_076_0864_0013, g32p_row02_traceSegment_076_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 891 13 14, g32p_row02_traceSegment_076_0891_0013, g32p_row02_traceSegment_076_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 864 27 27, g32p_row02_traceSegment_076_0864_0027, g32p_row02_traceSegment_076_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 918 13 14, g32p_row02_traceSegment_076_0918_0013, g32p_row02_traceSegment_076_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 945 13 14, g32p_row02_traceSegment_076_0945_0013, g32p_row02_traceSegment_076_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 918 27 27, g32p_row02_traceSegment_076_0918_0027, g32p_row02_traceSegment_076_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 864 54 54, g32p_row02_traceSegment_076_0864_0054, g32p_row02_traceSegment_076_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 972 13 14, g32p_row02_traceSegment_076_0972_0013, g32p_row02_traceSegment_076_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 999 13 14, g32p_row02_traceSegment_076_0999_0013, g32p_row02_traceSegment_076_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 972 27 27, g32p_row02_traceSegment_076_0972_0027, g32p_row02_traceSegment_076_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1026 13 14, g32p_row02_traceSegment_076_1026_0013, g32p_row02_traceSegment_076_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1053 13 14, g32p_row02_traceSegment_076_1053_0013, g32p_row02_traceSegment_076_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1026 27 27, g32p_row02_traceSegment_076_1026_0027, g32p_row02_traceSegment_076_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 972 54 54, g32p_row02_traceSegment_076_0972_0054, g32p_row02_traceSegment_076_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 864 108 108, g32p_row02_traceSegment_076_0864_0108, g32p_row02_traceSegment_076_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1080 13 14, g32p_row02_traceSegment_076_1080_0013, g32p_row02_traceSegment_076_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1107 13 14, g32p_row02_traceSegment_076_1107_0013, g32p_row02_traceSegment_076_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1080 27 27, g32p_row02_traceSegment_076_1080_0027, g32p_row02_traceSegment_076_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1134 13 14, g32p_row02_traceSegment_076_1134_0013, g32p_row02_traceSegment_076_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1161 13 14, g32p_row02_traceSegment_076_1161_0013, g32p_row02_traceSegment_076_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1134 27 27, g32p_row02_traceSegment_076_1134_0027, g32p_row02_traceSegment_076_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1080 54 54, g32p_row02_traceSegment_076_1080_0054, g32p_row02_traceSegment_076_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1188 13 14, g32p_row02_traceSegment_076_1188_0013, g32p_row02_traceSegment_076_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1215 13 14, g32p_row02_traceSegment_076_1215_0013, g32p_row02_traceSegment_076_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1188 27 27, g32p_row02_traceSegment_076_1188_0027, g32p_row02_traceSegment_076_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1242 13 14, g32p_row02_traceSegment_076_1242_0013, g32p_row02_traceSegment_076_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1269 13 14, g32p_row02_traceSegment_076_1269_0013, g32p_row02_traceSegment_076_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1242 27 27, g32p_row02_traceSegment_076_1242_0027, g32p_row02_traceSegment_076_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1188 54 54, g32p_row02_traceSegment_076_1188_0054, g32p_row02_traceSegment_076_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1080 108 108, g32p_row02_traceSegment_076_1080_0108, g32p_row02_traceSegment_076_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_076 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 864 216 216, g32p_row02_traceSegment_076_0864_0216, g32p_row02_traceSegment_076_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1296 13 14, g32p_row02_traceSegment_076_1296_0013, g32p_row02_traceSegment_076_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1323 13 14, g32p_row02_traceSegment_076_1323_0013, g32p_row02_traceSegment_076_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1296 27 27, g32p_row02_traceSegment_076_1296_0027, g32p_row02_traceSegment_076_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1350 13 14, g32p_row02_traceSegment_076_1350_0013, g32p_row02_traceSegment_076_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1377 13 14, g32p_row02_traceSegment_076_1377_0013, g32p_row02_traceSegment_076_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1350 27 27, g32p_row02_traceSegment_076_1350_0027, g32p_row02_traceSegment_076_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1296 54 54, g32p_row02_traceSegment_076_1296_0054, g32p_row02_traceSegment_076_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1404 13 14, g32p_row02_traceSegment_076_1404_0013, g32p_row02_traceSegment_076_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1431 13 14, g32p_row02_traceSegment_076_1431_0013, g32p_row02_traceSegment_076_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1404 27 27, g32p_row02_traceSegment_076_1404_0027, g32p_row02_traceSegment_076_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1458 13 14, g32p_row02_traceSegment_076_1458_0013, g32p_row02_traceSegment_076_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1485 13 14, g32p_row02_traceSegment_076_1485_0013, g32p_row02_traceSegment_076_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1458 27 27, g32p_row02_traceSegment_076_1458_0027, g32p_row02_traceSegment_076_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1404 54 54, g32p_row02_traceSegment_076_1404_0054, g32p_row02_traceSegment_076_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1296 108 108, g32p_row02_traceSegment_076_1296_0108, g32p_row02_traceSegment_076_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1512 13 14, g32p_row02_traceSegment_076_1512_0013, g32p_row02_traceSegment_076_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1552 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1539 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1539 13 14, g32p_row02_traceSegment_076_1539_0013, g32p_row02_traceSegment_076_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1512 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1512 27 27, g32p_row02_traceSegment_076_1512_0027, g32p_row02_traceSegment_076_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1566 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1566 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1566 13 14, g32p_row02_traceSegment_076_1566_0013, g32p_row02_traceSegment_076_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1593 13 14, g32p_row02_traceSegment_076_1593_0013, g32p_row02_traceSegment_076_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1566 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1566 27 27, g32p_row02_traceSegment_076_1566_0027, g32p_row02_traceSegment_076_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 1512 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1512 54 54, g32p_row02_traceSegment_076_1512_0054, g32p_row02_traceSegment_076_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1620 13 14, g32p_row02_traceSegment_076_1620_0013, g32p_row02_traceSegment_076_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1647 13 14, g32p_row02_traceSegment_076_1647_0013, g32p_row02_traceSegment_076_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1620 27 27, g32p_row02_traceSegment_076_1620_0027, g32p_row02_traceSegment_076_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1674 13 14, g32p_row02_traceSegment_076_1674_0013, g32p_row02_traceSegment_076_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1701 13 14, g32p_row02_traceSegment_076_1701_0013, g32p_row02_traceSegment_076_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1674 27 27, g32p_row02_traceSegment_076_1674_0027, g32p_row02_traceSegment_076_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1620 54 54, g32p_row02_traceSegment_076_1620_0054, g32p_row02_traceSegment_076_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 1512 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1512 108 108, g32p_row02_traceSegment_076_1512_0108, g32p_row02_traceSegment_076_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_076 1296 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1296 216 216, g32p_row02_traceSegment_076_1296_0216, g32p_row02_traceSegment_076_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_076 864 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 864 432 432, g32p_row02_traceSegment_076_0864_0432, g32p_row02_traceSegment_076_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_076 0 1728 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 0 864 864, g32p_row02_traceSegment_076_0000_0864, g32p_row02_traceSegment_076_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1728 13 14, g32p_row02_traceSegment_076_1728_0013, g32p_row02_traceSegment_076_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1755 13 14, g32p_row02_traceSegment_076_1755_0013, g32p_row02_traceSegment_076_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1728 27 27, g32p_row02_traceSegment_076_1728_0027, g32p_row02_traceSegment_076_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1782 13 14, g32p_row02_traceSegment_076_1782_0013, g32p_row02_traceSegment_076_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1809 13 14, g32p_row02_traceSegment_076_1809_0013, g32p_row02_traceSegment_076_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1782 27 27, g32p_row02_traceSegment_076_1782_0027, g32p_row02_traceSegment_076_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1728 54 54, g32p_row02_traceSegment_076_1728_0054, g32p_row02_traceSegment_076_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1836 13 14, g32p_row02_traceSegment_076_1836_0013, g32p_row02_traceSegment_076_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1863 13 14, g32p_row02_traceSegment_076_1863_0013, g32p_row02_traceSegment_076_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1836 27 27, g32p_row02_traceSegment_076_1836_0027, g32p_row02_traceSegment_076_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1890 13 14, g32p_row02_traceSegment_076_1890_0013, g32p_row02_traceSegment_076_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1917 13 14, g32p_row02_traceSegment_076_1917_0013, g32p_row02_traceSegment_076_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1890 27 27, g32p_row02_traceSegment_076_1890_0027, g32p_row02_traceSegment_076_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1836 54 54, g32p_row02_traceSegment_076_1836_0054, g32p_row02_traceSegment_076_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1728 108 108, g32p_row02_traceSegment_076_1728_0108, g32p_row02_traceSegment_076_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1944 13 14, g32p_row02_traceSegment_076_1944_0013, g32p_row02_traceSegment_076_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1971 13 14, g32p_row02_traceSegment_076_1971_0013, g32p_row02_traceSegment_076_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1944 27 27, g32p_row02_traceSegment_076_1944_0027, g32p_row02_traceSegment_076_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1998 13 14, g32p_row02_traceSegment_076_1998_0013, g32p_row02_traceSegment_076_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2025 13 14, g32p_row02_traceSegment_076_2025_0013, g32p_row02_traceSegment_076_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1998 27 27, g32p_row02_traceSegment_076_1998_0027, g32p_row02_traceSegment_076_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1944 54 54, g32p_row02_traceSegment_076_1944_0054, g32p_row02_traceSegment_076_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2052 13 14, g32p_row02_traceSegment_076_2052_0013, g32p_row02_traceSegment_076_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2079 13 14, g32p_row02_traceSegment_076_2079_0013, g32p_row02_traceSegment_076_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2052 27 27, g32p_row02_traceSegment_076_2052_0027, g32p_row02_traceSegment_076_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2106 13 14, g32p_row02_traceSegment_076_2106_0013, g32p_row02_traceSegment_076_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2133 13 14, g32p_row02_traceSegment_076_2133_0013, g32p_row02_traceSegment_076_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2106 27 27, g32p_row02_traceSegment_076_2106_0027, g32p_row02_traceSegment_076_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2052 54 54, g32p_row02_traceSegment_076_2052_0054, g32p_row02_traceSegment_076_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1944 108 108, g32p_row02_traceSegment_076_1944_0108, g32p_row02_traceSegment_076_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_076 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1728 216 216, g32p_row02_traceSegment_076_1728_0216, g32p_row02_traceSegment_076_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2160 13 14, g32p_row02_traceSegment_076_2160_0013, g32p_row02_traceSegment_076_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2187 13 14, g32p_row02_traceSegment_076_2187_0013, g32p_row02_traceSegment_076_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2160 27 27, g32p_row02_traceSegment_076_2160_0027, g32p_row02_traceSegment_076_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2214 13 14, g32p_row02_traceSegment_076_2214_0013, g32p_row02_traceSegment_076_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2241 13 14, g32p_row02_traceSegment_076_2241_0013, g32p_row02_traceSegment_076_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2214 27 27, g32p_row02_traceSegment_076_2214_0027, g32p_row02_traceSegment_076_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2160 54 54, g32p_row02_traceSegment_076_2160_0054, g32p_row02_traceSegment_076_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2268 13 14, g32p_row02_traceSegment_076_2268_0013, g32p_row02_traceSegment_076_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2295 13 14, g32p_row02_traceSegment_076_2295_0013, g32p_row02_traceSegment_076_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2268 27 27, g32p_row02_traceSegment_076_2268_0027, g32p_row02_traceSegment_076_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2322 13 14, g32p_row02_traceSegment_076_2322_0013, g32p_row02_traceSegment_076_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2349 13 14, g32p_row02_traceSegment_076_2349_0013, g32p_row02_traceSegment_076_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2322 27 27, g32p_row02_traceSegment_076_2322_0027, g32p_row02_traceSegment_076_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2268 54 54, g32p_row02_traceSegment_076_2268_0054, g32p_row02_traceSegment_076_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2160 108 108, g32p_row02_traceSegment_076_2160_0108, g32p_row02_traceSegment_076_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2376 13 14, g32p_row02_traceSegment_076_2376_0013, g32p_row02_traceSegment_076_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2403 13 14, g32p_row02_traceSegment_076_2403_0013, g32p_row02_traceSegment_076_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2376 27 27, g32p_row02_traceSegment_076_2376_0027, g32p_row02_traceSegment_076_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2430 13 14, g32p_row02_traceSegment_076_2430_0013, g32p_row02_traceSegment_076_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2470 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2457 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2457 13 14, g32p_row02_traceSegment_076_2457_0013, g32p_row02_traceSegment_076_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2430 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2430 27 27, g32p_row02_traceSegment_076_2430_0027, g32p_row02_traceSegment_076_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 2376 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2376 54 54, g32p_row02_traceSegment_076_2376_0054, g32p_row02_traceSegment_076_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2484 13 14, g32p_row02_traceSegment_076_2484_0013, g32p_row02_traceSegment_076_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2511 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2511 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2511 13 14, g32p_row02_traceSegment_076_2511_0013, g32p_row02_traceSegment_076_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2484 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2484 27 27, g32p_row02_traceSegment_076_2484_0027, g32p_row02_traceSegment_076_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2538 13 14, g32p_row02_traceSegment_076_2538_0013, g32p_row02_traceSegment_076_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2565 13 14, g32p_row02_traceSegment_076_2565_0013, g32p_row02_traceSegment_076_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2538 27 27, g32p_row02_traceSegment_076_2538_0027, g32p_row02_traceSegment_076_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 2484 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2484 54 54, g32p_row02_traceSegment_076_2484_0054, g32p_row02_traceSegment_076_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 2376 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2376 108 108, g32p_row02_traceSegment_076_2376_0108, g32p_row02_traceSegment_076_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_076 2160 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2160 216 216, g32p_row02_traceSegment_076_2160_0216, g32p_row02_traceSegment_076_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_076 1728 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1728 432 432, g32p_row02_traceSegment_076_1728_0432, g32p_row02_traceSegment_076_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2592 13 14, g32p_row02_traceSegment_076_2592_0013, g32p_row02_traceSegment_076_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2619 13 14, g32p_row02_traceSegment_076_2619_0013, g32p_row02_traceSegment_076_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2592 27 27, g32p_row02_traceSegment_076_2592_0027, g32p_row02_traceSegment_076_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2646 13 14, g32p_row02_traceSegment_076_2646_0013, g32p_row02_traceSegment_076_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2673 13 14, g32p_row02_traceSegment_076_2673_0013, g32p_row02_traceSegment_076_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2646 27 27, g32p_row02_traceSegment_076_2646_0027, g32p_row02_traceSegment_076_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2592 54 54, g32p_row02_traceSegment_076_2592_0054, g32p_row02_traceSegment_076_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2700 13 14, g32p_row02_traceSegment_076_2700_0013, g32p_row02_traceSegment_076_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2727 13 14, g32p_row02_traceSegment_076_2727_0013, g32p_row02_traceSegment_076_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2700 27 27, g32p_row02_traceSegment_076_2700_0027, g32p_row02_traceSegment_076_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2767 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2754 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2754 13 14, g32p_row02_traceSegment_076_2754_0013, g32p_row02_traceSegment_076_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2781 13 14, g32p_row02_traceSegment_076_2781_0013, g32p_row02_traceSegment_076_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2754 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2754 27 27, g32p_row02_traceSegment_076_2754_0027, g32p_row02_traceSegment_076_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 2700 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2700 54 54, g32p_row02_traceSegment_076_2700_0054, g32p_row02_traceSegment_076_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 2592 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2592 108 108, g32p_row02_traceSegment_076_2592_0108, g32p_row02_traceSegment_076_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2808 13 14, g32p_row02_traceSegment_076_2808_0013, g32p_row02_traceSegment_076_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2835 13 14, g32p_row02_traceSegment_076_2835_0013, g32p_row02_traceSegment_076_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2808 27 27, g32p_row02_traceSegment_076_2808_0027, g32p_row02_traceSegment_076_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2862 13 14, g32p_row02_traceSegment_076_2862_0013, g32p_row02_traceSegment_076_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2889 13 14, g32p_row02_traceSegment_076_2889_0013, g32p_row02_traceSegment_076_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2862 27 27, g32p_row02_traceSegment_076_2862_0027, g32p_row02_traceSegment_076_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2808 54 54, g32p_row02_traceSegment_076_2808_0054, g32p_row02_traceSegment_076_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2916 13 14, g32p_row02_traceSegment_076_2916_0013, g32p_row02_traceSegment_076_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2943 13 14, g32p_row02_traceSegment_076_2943_0013, g32p_row02_traceSegment_076_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2916 27 27, g32p_row02_traceSegment_076_2916_0027, g32p_row02_traceSegment_076_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2970 13 14, g32p_row02_traceSegment_076_2970_0013, g32p_row02_traceSegment_076_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2997 13 14, g32p_row02_traceSegment_076_2997_0013, g32p_row02_traceSegment_076_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2970 27 27, g32p_row02_traceSegment_076_2970_0027, g32p_row02_traceSegment_076_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2916 54 54, g32p_row02_traceSegment_076_2916_0054, g32p_row02_traceSegment_076_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2808 108 108, g32p_row02_traceSegment_076_2808_0108, g32p_row02_traceSegment_076_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_076 2592 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2592 216 216, g32p_row02_traceSegment_076_2592_0216, g32p_row02_traceSegment_076_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3024 13 14, g32p_row02_traceSegment_076_3024_0013, g32p_row02_traceSegment_076_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3051 13 14, g32p_row02_traceSegment_076_3051_0013, g32p_row02_traceSegment_076_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3024 27 27, g32p_row02_traceSegment_076_3024_0027, g32p_row02_traceSegment_076_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3078 13 14, g32p_row02_traceSegment_076_3078_0013, g32p_row02_traceSegment_076_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3105 13 14, g32p_row02_traceSegment_076_3105_0013, g32p_row02_traceSegment_076_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3078 27 27, g32p_row02_traceSegment_076_3078_0027, g32p_row02_traceSegment_076_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3024 54 54, g32p_row02_traceSegment_076_3024_0054, g32p_row02_traceSegment_076_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3145 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3132 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3132 13 14, g32p_row02_traceSegment_076_3132_0013, g32p_row02_traceSegment_076_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3159 13 14, g32p_row02_traceSegment_076_3159_0013, g32p_row02_traceSegment_076_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 3132 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3132 27 27, g32p_row02_traceSegment_076_3132_0027, g32p_row02_traceSegment_076_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3186 13 14, g32p_row02_traceSegment_076_3186_0013, g32p_row02_traceSegment_076_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3213 13 14, g32p_row02_traceSegment_076_3213_0013, g32p_row02_traceSegment_076_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3186 27 27, g32p_row02_traceSegment_076_3186_0027, g32p_row02_traceSegment_076_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 3132 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3132 54 54, g32p_row02_traceSegment_076_3132_0054, g32p_row02_traceSegment_076_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 3024 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3024 108 108, g32p_row02_traceSegment_076_3024_0108, g32p_row02_traceSegment_076_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3240 13 14, g32p_row02_traceSegment_076_3240_0013, g32p_row02_traceSegment_076_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3267 13 14, g32p_row02_traceSegment_076_3267_0013, g32p_row02_traceSegment_076_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3240 27 27, g32p_row02_traceSegment_076_3240_0027, g32p_row02_traceSegment_076_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3294 13 14, g32p_row02_traceSegment_076_3294_0013, g32p_row02_traceSegment_076_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3321 13 14, g32p_row02_traceSegment_076_3321_0013, g32p_row02_traceSegment_076_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3294 27 27, g32p_row02_traceSegment_076_3294_0027, g32p_row02_traceSegment_076_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3240 54 54, g32p_row02_traceSegment_076_3240_0054, g32p_row02_traceSegment_076_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3348 13 14, g32p_row02_traceSegment_076_3348_0013, g32p_row02_traceSegment_076_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3375 13 14, g32p_row02_traceSegment_076_3375_0013, g32p_row02_traceSegment_076_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3348 27 27, g32p_row02_traceSegment_076_3348_0027, g32p_row02_traceSegment_076_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3402 13 14, g32p_row02_traceSegment_076_3402_0013, g32p_row02_traceSegment_076_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_076 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_076 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_076_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_076 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3429 13 14, g32p_row02_traceSegment_076_3429_0013, g32p_row02_traceSegment_076_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_076 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3402 27 27, g32p_row02_traceSegment_076_3402_0027, g32p_row02_traceSegment_076_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_076 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3348 54 54, g32p_row02_traceSegment_076_3348_0054, g32p_row02_traceSegment_076_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_076 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3240 108 108, g32p_row02_traceSegment_076_3240_0108, g32p_row02_traceSegment_076_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_076_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_076 3024 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 3024 216 216, g32p_row02_traceSegment_076_3024_0216, g32p_row02_traceSegment_076_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_076_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_076 2592 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 2592 432 432, g32p_row02_traceSegment_076_2592_0432, g32p_row02_traceSegment_076_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_076_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_076 1728 1728 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 1728 864 864, g32p_row02_traceSegment_076_1728_0864, g32p_row02_traceSegment_076_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_076_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_076 0 3456 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_076 0 1728 1728, g32p_row02_traceSegment_076_0000_1728, g32p_row02_traceSegment_076_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 76 = [0, 0, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_076_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_077 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 77 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_077_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 0 13 14, g32p_row02_traceSegment_077_0000_0013, g32p_row02_traceSegment_077_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 27 13 14, g32p_row02_traceSegment_077_0027_0013, g32p_row02_traceSegment_077_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 0 27 27, g32p_row02_traceSegment_077_0000_0027, g32p_row02_traceSegment_077_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 54 13 14, g32p_row02_traceSegment_077_0054_0013, g32p_row02_traceSegment_077_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 81 13 14, g32p_row02_traceSegment_077_0081_0013, g32p_row02_traceSegment_077_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 54 27 27, g32p_row02_traceSegment_077_0054_0027, g32p_row02_traceSegment_077_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 0 54 54, g32p_row02_traceSegment_077_0000_0054, g32p_row02_traceSegment_077_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 108 13 14, g32p_row02_traceSegment_077_0108_0013, g32p_row02_traceSegment_077_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 135 13 14, g32p_row02_traceSegment_077_0135_0013, g32p_row02_traceSegment_077_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 108 27 27, g32p_row02_traceSegment_077_0108_0027, g32p_row02_traceSegment_077_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 162 13 14, g32p_row02_traceSegment_077_0162_0013, g32p_row02_traceSegment_077_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 189 13 14, g32p_row02_traceSegment_077_0189_0013, g32p_row02_traceSegment_077_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 162 27 27, g32p_row02_traceSegment_077_0162_0027, g32p_row02_traceSegment_077_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 108 54 54, g32p_row02_traceSegment_077_0108_0054, g32p_row02_traceSegment_077_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 0 108 108, g32p_row02_traceSegment_077_0000_0108, g32p_row02_traceSegment_077_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 216 13 14, g32p_row02_traceSegment_077_0216_0013, g32p_row02_traceSegment_077_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 243 13 14, g32p_row02_traceSegment_077_0243_0013, g32p_row02_traceSegment_077_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 216 27 27, g32p_row02_traceSegment_077_0216_0027, g32p_row02_traceSegment_077_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 270 13 14, g32p_row02_traceSegment_077_0270_0013, g32p_row02_traceSegment_077_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 297 13 14, g32p_row02_traceSegment_077_0297_0013, g32p_row02_traceSegment_077_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 270 27 27, g32p_row02_traceSegment_077_0270_0027, g32p_row02_traceSegment_077_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 216 54 54, g32p_row02_traceSegment_077_0216_0054, g32p_row02_traceSegment_077_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 324 13 14, g32p_row02_traceSegment_077_0324_0013, g32p_row02_traceSegment_077_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 351 13 14, g32p_row02_traceSegment_077_0351_0013, g32p_row02_traceSegment_077_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 324 27 27, g32p_row02_traceSegment_077_0324_0027, g32p_row02_traceSegment_077_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 378 13 14, g32p_row02_traceSegment_077_0378_0013, g32p_row02_traceSegment_077_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 405 13 14, g32p_row02_traceSegment_077_0405_0013, g32p_row02_traceSegment_077_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 378 27 27, g32p_row02_traceSegment_077_0378_0027, g32p_row02_traceSegment_077_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 324 54 54, g32p_row02_traceSegment_077_0324_0054, g32p_row02_traceSegment_077_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 216 108 108, g32p_row02_traceSegment_077_0216_0108, g32p_row02_traceSegment_077_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_077 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 0 216 216, g32p_row02_traceSegment_077_0000_0216, g32p_row02_traceSegment_077_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 432 13 14, g32p_row02_traceSegment_077_0432_0013, g32p_row02_traceSegment_077_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 459 13 14, g32p_row02_traceSegment_077_0459_0013, g32p_row02_traceSegment_077_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 432 27 27, g32p_row02_traceSegment_077_0432_0027, g32p_row02_traceSegment_077_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 486 13 14, g32p_row02_traceSegment_077_0486_0013, g32p_row02_traceSegment_077_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 513 13 14, g32p_row02_traceSegment_077_0513_0013, g32p_row02_traceSegment_077_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 486 27 27, g32p_row02_traceSegment_077_0486_0027, g32p_row02_traceSegment_077_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 432 54 54, g32p_row02_traceSegment_077_0432_0054, g32p_row02_traceSegment_077_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 540 13 14, g32p_row02_traceSegment_077_0540_0013, g32p_row02_traceSegment_077_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 567 13 14, g32p_row02_traceSegment_077_0567_0013, g32p_row02_traceSegment_077_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 540 27 27, g32p_row02_traceSegment_077_0540_0027, g32p_row02_traceSegment_077_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 594 13 14, g32p_row02_traceSegment_077_0594_0013, g32p_row02_traceSegment_077_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 621 13 14, g32p_row02_traceSegment_077_0621_0013, g32p_row02_traceSegment_077_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 594 27 27, g32p_row02_traceSegment_077_0594_0027, g32p_row02_traceSegment_077_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 540 54 54, g32p_row02_traceSegment_077_0540_0054, g32p_row02_traceSegment_077_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 432 108 108, g32p_row02_traceSegment_077_0432_0108, g32p_row02_traceSegment_077_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 648 13 14, g32p_row02_traceSegment_077_0648_0013, g32p_row02_traceSegment_077_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 675 13 14, g32p_row02_traceSegment_077_0675_0013, g32p_row02_traceSegment_077_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 648 27 27, g32p_row02_traceSegment_077_0648_0027, g32p_row02_traceSegment_077_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 702 13 14, g32p_row02_traceSegment_077_0702_0013, g32p_row02_traceSegment_077_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 729 13 14, g32p_row02_traceSegment_077_0729_0013, g32p_row02_traceSegment_077_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 702 27 27, g32p_row02_traceSegment_077_0702_0027, g32p_row02_traceSegment_077_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 648 54 54, g32p_row02_traceSegment_077_0648_0054, g32p_row02_traceSegment_077_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 756 13 14, g32p_row02_traceSegment_077_0756_0013, g32p_row02_traceSegment_077_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 783 13 14, g32p_row02_traceSegment_077_0783_0013, g32p_row02_traceSegment_077_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 756 27 27, g32p_row02_traceSegment_077_0756_0027, g32p_row02_traceSegment_077_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 810 13 14, g32p_row02_traceSegment_077_0810_0013, g32p_row02_traceSegment_077_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 837 13 14, g32p_row02_traceSegment_077_0837_0013, g32p_row02_traceSegment_077_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 810 27 27, g32p_row02_traceSegment_077_0810_0027, g32p_row02_traceSegment_077_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 756 54 54, g32p_row02_traceSegment_077_0756_0054, g32p_row02_traceSegment_077_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 648 108 108, g32p_row02_traceSegment_077_0648_0108, g32p_row02_traceSegment_077_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_077 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 432 216 216, g32p_row02_traceSegment_077_0432_0216, g32p_row02_traceSegment_077_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_077 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 0 432 432, g32p_row02_traceSegment_077_0000_0432, g32p_row02_traceSegment_077_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 864 13 14, g32p_row02_traceSegment_077_0864_0013, g32p_row02_traceSegment_077_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 891 13 14, g32p_row02_traceSegment_077_0891_0013, g32p_row02_traceSegment_077_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 864 27 27, g32p_row02_traceSegment_077_0864_0027, g32p_row02_traceSegment_077_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 918 13 14, g32p_row02_traceSegment_077_0918_0013, g32p_row02_traceSegment_077_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 945 13 14, g32p_row02_traceSegment_077_0945_0013, g32p_row02_traceSegment_077_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 918 27 27, g32p_row02_traceSegment_077_0918_0027, g32p_row02_traceSegment_077_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 864 54 54, g32p_row02_traceSegment_077_0864_0054, g32p_row02_traceSegment_077_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 972 13 14, g32p_row02_traceSegment_077_0972_0013, g32p_row02_traceSegment_077_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 999 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 999 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 999 13 14, g32p_row02_traceSegment_077_0999_0013, g32p_row02_traceSegment_077_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 972 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 972 27 27, g32p_row02_traceSegment_077_0972_0027, g32p_row02_traceSegment_077_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1026 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1026 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1026 13 14, g32p_row02_traceSegment_077_1026_0013, g32p_row02_traceSegment_077_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1053 13 14, g32p_row02_traceSegment_077_1053_0013, g32p_row02_traceSegment_077_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1026 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1026 27 27, g32p_row02_traceSegment_077_1026_0027, g32p_row02_traceSegment_077_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 972 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 972 54 54, g32p_row02_traceSegment_077_0972_0054, g32p_row02_traceSegment_077_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 864 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 864 108 108, g32p_row02_traceSegment_077_0864_0108, g32p_row02_traceSegment_077_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1080 13 14, g32p_row02_traceSegment_077_1080_0013, g32p_row02_traceSegment_077_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1107 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1107 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1107 13 14, g32p_row02_traceSegment_077_1107_0013, g32p_row02_traceSegment_077_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1080 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1080 27 27, g32p_row02_traceSegment_077_1080_0027, g32p_row02_traceSegment_077_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1134 13 14, g32p_row02_traceSegment_077_1134_0013, g32p_row02_traceSegment_077_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1161 13 14, g32p_row02_traceSegment_077_1161_0013, g32p_row02_traceSegment_077_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1134 27 27, g32p_row02_traceSegment_077_1134_0027, g32p_row02_traceSegment_077_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 1080 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1080 54 54, g32p_row02_traceSegment_077_1080_0054, g32p_row02_traceSegment_077_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1188 13 14, g32p_row02_traceSegment_077_1188_0013, g32p_row02_traceSegment_077_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1215 13 14, g32p_row02_traceSegment_077_1215_0013, g32p_row02_traceSegment_077_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1188 27 27, g32p_row02_traceSegment_077_1188_0027, g32p_row02_traceSegment_077_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1242 13 14, g32p_row02_traceSegment_077_1242_0013, g32p_row02_traceSegment_077_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1269 13 14, g32p_row02_traceSegment_077_1269_0013, g32p_row02_traceSegment_077_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1242 27 27, g32p_row02_traceSegment_077_1242_0027, g32p_row02_traceSegment_077_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1188 54 54, g32p_row02_traceSegment_077_1188_0054, g32p_row02_traceSegment_077_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 1080 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1080 108 108, g32p_row02_traceSegment_077_1080_0108, g32p_row02_traceSegment_077_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_077 864 432 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 864 216 216, g32p_row02_traceSegment_077_0864_0216, g32p_row02_traceSegment_077_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1296 13 14, g32p_row02_traceSegment_077_1296_0013, g32p_row02_traceSegment_077_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1336 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1323 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1323 13 14, g32p_row02_traceSegment_077_1323_0013, g32p_row02_traceSegment_077_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1296 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1296 27 27, g32p_row02_traceSegment_077_1296_0027, g32p_row02_traceSegment_077_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1350 13 14, g32p_row02_traceSegment_077_1350_0013, g32p_row02_traceSegment_077_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1377 13 14, g32p_row02_traceSegment_077_1377_0013, g32p_row02_traceSegment_077_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1350 27 27, g32p_row02_traceSegment_077_1350_0027, g32p_row02_traceSegment_077_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 1296 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1296 54 54, g32p_row02_traceSegment_077_1296_0054, g32p_row02_traceSegment_077_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1404 13 14, g32p_row02_traceSegment_077_1404_0013, g32p_row02_traceSegment_077_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1431 13 14, g32p_row02_traceSegment_077_1431_0013, g32p_row02_traceSegment_077_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1404 27 27, g32p_row02_traceSegment_077_1404_0027, g32p_row02_traceSegment_077_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1458 13 14, g32p_row02_traceSegment_077_1458_0013, g32p_row02_traceSegment_077_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1485 13 14, g32p_row02_traceSegment_077_1485_0013, g32p_row02_traceSegment_077_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1458 27 27, g32p_row02_traceSegment_077_1458_0027, g32p_row02_traceSegment_077_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1404 54 54, g32p_row02_traceSegment_077_1404_0054, g32p_row02_traceSegment_077_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 1296 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1296 108 108, g32p_row02_traceSegment_077_1296_0108, g32p_row02_traceSegment_077_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1512 13 14, g32p_row02_traceSegment_077_1512_0013, g32p_row02_traceSegment_077_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1539 13 14, g32p_row02_traceSegment_077_1539_0013, g32p_row02_traceSegment_077_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1512 27 27, g32p_row02_traceSegment_077_1512_0027, g32p_row02_traceSegment_077_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1566 13 14, g32p_row02_traceSegment_077_1566_0013, g32p_row02_traceSegment_077_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1593 13 14, g32p_row02_traceSegment_077_1593_0013, g32p_row02_traceSegment_077_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1566 27 27, g32p_row02_traceSegment_077_1566_0027, g32p_row02_traceSegment_077_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1512 54 54, g32p_row02_traceSegment_077_1512_0054, g32p_row02_traceSegment_077_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1620 13 14, g32p_row02_traceSegment_077_1620_0013, g32p_row02_traceSegment_077_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1647 13 14, g32p_row02_traceSegment_077_1647_0013, g32p_row02_traceSegment_077_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1620 27 27, g32p_row02_traceSegment_077_1620_0027, g32p_row02_traceSegment_077_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1674 13 14, g32p_row02_traceSegment_077_1674_0013, g32p_row02_traceSegment_077_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1701 13 14, g32p_row02_traceSegment_077_1701_0013, g32p_row02_traceSegment_077_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1674 27 27, g32p_row02_traceSegment_077_1674_0027, g32p_row02_traceSegment_077_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1620 54 54, g32p_row02_traceSegment_077_1620_0054, g32p_row02_traceSegment_077_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1512 108 108, g32p_row02_traceSegment_077_1512_0108, g32p_row02_traceSegment_077_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_077 1296 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1296 216 216, g32p_row02_traceSegment_077_1296_0216, g32p_row02_traceSegment_077_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_077 864 864 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 864 432 432, g32p_row02_traceSegment_077_0864_0432, g32p_row02_traceSegment_077_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_077 0 1728 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 0 864 864, g32p_row02_traceSegment_077_0000_0864, g32p_row02_traceSegment_077_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1728 13 14, g32p_row02_traceSegment_077_1728_0013, g32p_row02_traceSegment_077_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1755 13 14, g32p_row02_traceSegment_077_1755_0013, g32p_row02_traceSegment_077_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1728 27 27, g32p_row02_traceSegment_077_1728_0027, g32p_row02_traceSegment_077_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1782 13 14, g32p_row02_traceSegment_077_1782_0013, g32p_row02_traceSegment_077_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1809 13 14, g32p_row02_traceSegment_077_1809_0013, g32p_row02_traceSegment_077_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1782 27 27, g32p_row02_traceSegment_077_1782_0027, g32p_row02_traceSegment_077_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1728 54 54, g32p_row02_traceSegment_077_1728_0054, g32p_row02_traceSegment_077_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1836 13 14, g32p_row02_traceSegment_077_1836_0013, g32p_row02_traceSegment_077_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1863 13 14, g32p_row02_traceSegment_077_1863_0013, g32p_row02_traceSegment_077_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1836 27 27, g32p_row02_traceSegment_077_1836_0027, g32p_row02_traceSegment_077_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1890 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1890 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1890 13 14, g32p_row02_traceSegment_077_1890_0013, g32p_row02_traceSegment_077_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1917 13 14, g32p_row02_traceSegment_077_1917_0013, g32p_row02_traceSegment_077_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1890 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1890 27 27, g32p_row02_traceSegment_077_1890_0027, g32p_row02_traceSegment_077_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 1836 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1836 54 54, g32p_row02_traceSegment_077_1836_0054, g32p_row02_traceSegment_077_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 1728 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1728 108 108, g32p_row02_traceSegment_077_1728_0108, g32p_row02_traceSegment_077_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1944 13 14, g32p_row02_traceSegment_077_1944_0013, g32p_row02_traceSegment_077_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1971 13 14, g32p_row02_traceSegment_077_1971_0013, g32p_row02_traceSegment_077_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1944 27 27, g32p_row02_traceSegment_077_1944_0027, g32p_row02_traceSegment_077_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1998 13 14, g32p_row02_traceSegment_077_1998_0013, g32p_row02_traceSegment_077_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2025 13 14, g32p_row02_traceSegment_077_2025_0013, g32p_row02_traceSegment_077_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1998 27 27, g32p_row02_traceSegment_077_1998_0027, g32p_row02_traceSegment_077_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1944 54 54, g32p_row02_traceSegment_077_1944_0054, g32p_row02_traceSegment_077_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2052 13 14, g32p_row02_traceSegment_077_2052_0013, g32p_row02_traceSegment_077_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2079 13 14, g32p_row02_traceSegment_077_2079_0013, g32p_row02_traceSegment_077_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2052 27 27, g32p_row02_traceSegment_077_2052_0027, g32p_row02_traceSegment_077_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2106 13 14, g32p_row02_traceSegment_077_2106_0013, g32p_row02_traceSegment_077_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2133 13 14, g32p_row02_traceSegment_077_2133_0013, g32p_row02_traceSegment_077_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2106 27 27, g32p_row02_traceSegment_077_2106_0027, g32p_row02_traceSegment_077_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2052 54 54, g32p_row02_traceSegment_077_2052_0054, g32p_row02_traceSegment_077_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1944 108 108, g32p_row02_traceSegment_077_1944_0108, g32p_row02_traceSegment_077_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_077 1728 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1728 216 216, g32p_row02_traceSegment_077_1728_0216, g32p_row02_traceSegment_077_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2160 13 14, g32p_row02_traceSegment_077_2160_0013, g32p_row02_traceSegment_077_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2187 13 14, g32p_row02_traceSegment_077_2187_0013, g32p_row02_traceSegment_077_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2160 27 27, g32p_row02_traceSegment_077_2160_0027, g32p_row02_traceSegment_077_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2214 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2214 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2214 13 14, g32p_row02_traceSegment_077_2214_0013, g32p_row02_traceSegment_077_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2241 13 14, g32p_row02_traceSegment_077_2241_0013, g32p_row02_traceSegment_077_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2214 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2214 27 27, g32p_row02_traceSegment_077_2214_0027, g32p_row02_traceSegment_077_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 2160 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2160 54 54, g32p_row02_traceSegment_077_2160_0054, g32p_row02_traceSegment_077_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2268 13 14, g32p_row02_traceSegment_077_2268_0013, g32p_row02_traceSegment_077_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2295 13 14, g32p_row02_traceSegment_077_2295_0013, g32p_row02_traceSegment_077_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2268 27 27, g32p_row02_traceSegment_077_2268_0027, g32p_row02_traceSegment_077_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2322 13 14, g32p_row02_traceSegment_077_2322_0013, g32p_row02_traceSegment_077_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2349 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2349 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2349 13 14, g32p_row02_traceSegment_077_2349_0013, g32p_row02_traceSegment_077_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2322 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2322 27 27, g32p_row02_traceSegment_077_2322_0027, g32p_row02_traceSegment_077_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 2268 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2268 54 54, g32p_row02_traceSegment_077_2268_0054, g32p_row02_traceSegment_077_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 2160 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2160 108 108, g32p_row02_traceSegment_077_2160_0108, g32p_row02_traceSegment_077_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2376 13 14, g32p_row02_traceSegment_077_2376_0013, g32p_row02_traceSegment_077_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2403 13 14, g32p_row02_traceSegment_077_2403_0013, g32p_row02_traceSegment_077_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2376 27 27, g32p_row02_traceSegment_077_2376_0027, g32p_row02_traceSegment_077_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2430 13 14, g32p_row02_traceSegment_077_2430_0013, g32p_row02_traceSegment_077_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2457 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2457 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2457 13 14, g32p_row02_traceSegment_077_2457_0013, g32p_row02_traceSegment_077_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2430 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2430 27 27, g32p_row02_traceSegment_077_2430_0027, g32p_row02_traceSegment_077_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 2376 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2376 54 54, g32p_row02_traceSegment_077_2376_0054, g32p_row02_traceSegment_077_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2484 13 14, g32p_row02_traceSegment_077_2484_0013, g32p_row02_traceSegment_077_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2511 13 14, g32p_row02_traceSegment_077_2511_0013, g32p_row02_traceSegment_077_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2484 27 27, g32p_row02_traceSegment_077_2484_0027, g32p_row02_traceSegment_077_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2538 13 14, g32p_row02_traceSegment_077_2538_0013, g32p_row02_traceSegment_077_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2565 13 14, g32p_row02_traceSegment_077_2565_0013, g32p_row02_traceSegment_077_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2538 27 27, g32p_row02_traceSegment_077_2538_0027, g32p_row02_traceSegment_077_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2484 54 54, g32p_row02_traceSegment_077_2484_0054, g32p_row02_traceSegment_077_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 2376 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2376 108 108, g32p_row02_traceSegment_077_2376_0108, g32p_row02_traceSegment_077_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_077 2160 432 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2160 216 216, g32p_row02_traceSegment_077_2160_0216, g32p_row02_traceSegment_077_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_077 1728 864 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1728 432 432, g32p_row02_traceSegment_077_1728_0432, g32p_row02_traceSegment_077_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2592 13 14, g32p_row02_traceSegment_077_2592_0013, g32p_row02_traceSegment_077_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2619 13 14, g32p_row02_traceSegment_077_2619_0013, g32p_row02_traceSegment_077_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2592 27 27, g32p_row02_traceSegment_077_2592_0027, g32p_row02_traceSegment_077_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2646 13 14, g32p_row02_traceSegment_077_2646_0013, g32p_row02_traceSegment_077_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2673 13 14, g32p_row02_traceSegment_077_2673_0013, g32p_row02_traceSegment_077_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2646 27 27, g32p_row02_traceSegment_077_2646_0027, g32p_row02_traceSegment_077_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2592 54 54, g32p_row02_traceSegment_077_2592_0054, g32p_row02_traceSegment_077_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2700 13 14, g32p_row02_traceSegment_077_2700_0013, g32p_row02_traceSegment_077_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2727 13 14, g32p_row02_traceSegment_077_2727_0013, g32p_row02_traceSegment_077_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2700 27 27, g32p_row02_traceSegment_077_2700_0027, g32p_row02_traceSegment_077_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2754 13 14, g32p_row02_traceSegment_077_2754_0013, g32p_row02_traceSegment_077_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2781 13 14, g32p_row02_traceSegment_077_2781_0013, g32p_row02_traceSegment_077_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2754 27 27, g32p_row02_traceSegment_077_2754_0027, g32p_row02_traceSegment_077_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2700 54 54, g32p_row02_traceSegment_077_2700_0054, g32p_row02_traceSegment_077_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2592 108 108, g32p_row02_traceSegment_077_2592_0108, g32p_row02_traceSegment_077_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2808 13 14, g32p_row02_traceSegment_077_2808_0013, g32p_row02_traceSegment_077_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2835 13 14, g32p_row02_traceSegment_077_2835_0013, g32p_row02_traceSegment_077_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2808 27 27, g32p_row02_traceSegment_077_2808_0027, g32p_row02_traceSegment_077_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2862 13 14, g32p_row02_traceSegment_077_2862_0013, g32p_row02_traceSegment_077_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2889 13 14, g32p_row02_traceSegment_077_2889_0013, g32p_row02_traceSegment_077_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2862 27 27, g32p_row02_traceSegment_077_2862_0027, g32p_row02_traceSegment_077_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2808 54 54, g32p_row02_traceSegment_077_2808_0054, g32p_row02_traceSegment_077_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2916 13 14, g32p_row02_traceSegment_077_2916_0013, g32p_row02_traceSegment_077_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2943 13 14, g32p_row02_traceSegment_077_2943_0013, g32p_row02_traceSegment_077_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2916 27 27, g32p_row02_traceSegment_077_2916_0027, g32p_row02_traceSegment_077_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2970 13 14, g32p_row02_traceSegment_077_2970_0013, g32p_row02_traceSegment_077_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2997 13 14, g32p_row02_traceSegment_077_2997_0013, g32p_row02_traceSegment_077_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2970 27 27, g32p_row02_traceSegment_077_2970_0027, g32p_row02_traceSegment_077_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2916 54 54, g32p_row02_traceSegment_077_2916_0054, g32p_row02_traceSegment_077_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2808 108 108, g32p_row02_traceSegment_077_2808_0108, g32p_row02_traceSegment_077_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_077 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2592 216 216, g32p_row02_traceSegment_077_2592_0216, g32p_row02_traceSegment_077_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3024 13 14, g32p_row02_traceSegment_077_3024_0013, g32p_row02_traceSegment_077_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3051 13 14, g32p_row02_traceSegment_077_3051_0013, g32p_row02_traceSegment_077_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3024 27 27, g32p_row02_traceSegment_077_3024_0027, g32p_row02_traceSegment_077_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3078 13 14, g32p_row02_traceSegment_077_3078_0013, g32p_row02_traceSegment_077_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3105 13 14, g32p_row02_traceSegment_077_3105_0013, g32p_row02_traceSegment_077_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3078 27 27, g32p_row02_traceSegment_077_3078_0027, g32p_row02_traceSegment_077_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3024 54 54, g32p_row02_traceSegment_077_3024_0054, g32p_row02_traceSegment_077_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3132 13 14, g32p_row02_traceSegment_077_3132_0013, g32p_row02_traceSegment_077_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3159 13 14, g32p_row02_traceSegment_077_3159_0013, g32p_row02_traceSegment_077_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3132 27 27, g32p_row02_traceSegment_077_3132_0027, g32p_row02_traceSegment_077_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3186 13 14, g32p_row02_traceSegment_077_3186_0013, g32p_row02_traceSegment_077_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3213 13 14, g32p_row02_traceSegment_077_3213_0013, g32p_row02_traceSegment_077_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3186 27 27, g32p_row02_traceSegment_077_3186_0027, g32p_row02_traceSegment_077_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3132 54 54, g32p_row02_traceSegment_077_3132_0054, g32p_row02_traceSegment_077_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3024 108 108, g32p_row02_traceSegment_077_3024_0108, g32p_row02_traceSegment_077_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3240 13 14, g32p_row02_traceSegment_077_3240_0013, g32p_row02_traceSegment_077_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3267 13 14, g32p_row02_traceSegment_077_3267_0013, g32p_row02_traceSegment_077_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3240 27 27, g32p_row02_traceSegment_077_3240_0027, g32p_row02_traceSegment_077_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3294 13 14, g32p_row02_traceSegment_077_3294_0013, g32p_row02_traceSegment_077_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3321 13 14, g32p_row02_traceSegment_077_3321_0013, g32p_row02_traceSegment_077_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3294 27 27, g32p_row02_traceSegment_077_3294_0027, g32p_row02_traceSegment_077_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3240 54 54, g32p_row02_traceSegment_077_3240_0054, g32p_row02_traceSegment_077_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3348 13 14, g32p_row02_traceSegment_077_3348_0013, g32p_row02_traceSegment_077_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3375 13 14, g32p_row02_traceSegment_077_3375_0013, g32p_row02_traceSegment_077_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3348 27 27, g32p_row02_traceSegment_077_3348_0027, g32p_row02_traceSegment_077_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3402 13 14, g32p_row02_traceSegment_077_3402_0013, g32p_row02_traceSegment_077_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_077 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_077 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_077_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_077 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3429 13 14, g32p_row02_traceSegment_077_3429_0013, g32p_row02_traceSegment_077_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_077 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3402 27 27, g32p_row02_traceSegment_077_3402_0027, g32p_row02_traceSegment_077_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_077 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3348 54 54, g32p_row02_traceSegment_077_3348_0054, g32p_row02_traceSegment_077_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_077 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3240 108 108, g32p_row02_traceSegment_077_3240_0108, g32p_row02_traceSegment_077_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_077_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_077 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 3024 216 216, g32p_row02_traceSegment_077_3024_0216, g32p_row02_traceSegment_077_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_077_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_077 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 2592 432 432, g32p_row02_traceSegment_077_2592_0432, g32p_row02_traceSegment_077_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_077_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_077 1728 1728 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 1728 864 864, g32p_row02_traceSegment_077_1728_0864, g32p_row02_traceSegment_077_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_077_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_077 0 3456 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_077 0 1728 1728, g32p_row02_traceSegment_077_0000_1728, g32p_row02_traceSegment_077_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 77 = [0, 0, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_077_0000_3456

end HodgeLean.Foundations.Program

end
end
