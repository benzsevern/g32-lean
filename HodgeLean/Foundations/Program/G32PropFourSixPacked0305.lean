import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0304

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_067 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 67 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_067_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 13 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 0 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 0 13 14, g32p_row02_traceSegment_067_0000_0013, g32p_row02_traceSegment_067_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 27 13 14, g32p_row02_traceSegment_067_0027_0013, g32p_row02_traceSegment_067_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 0 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 0 27 27, g32p_row02_traceSegment_067_0000_0027, g32p_row02_traceSegment_067_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 54 13 14, g32p_row02_traceSegment_067_0054_0013, g32p_row02_traceSegment_067_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 81 13 14, g32p_row02_traceSegment_067_0081_0013, g32p_row02_traceSegment_067_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 54 27 27, g32p_row02_traceSegment_067_0054_0027, g32p_row02_traceSegment_067_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 0 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 0 54 54, g32p_row02_traceSegment_067_0000_0054, g32p_row02_traceSegment_067_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 108 13 14, g32p_row02_traceSegment_067_0108_0013, g32p_row02_traceSegment_067_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 135 13 14, g32p_row02_traceSegment_067_0135_0013, g32p_row02_traceSegment_067_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 108 27 27, g32p_row02_traceSegment_067_0108_0027, g32p_row02_traceSegment_067_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 162 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 162 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 162 13 14, g32p_row02_traceSegment_067_0162_0013, g32p_row02_traceSegment_067_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 189 13 14, g32p_row02_traceSegment_067_0189_0013, g32p_row02_traceSegment_067_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 162 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 162 27 27, g32p_row02_traceSegment_067_0162_0027, g32p_row02_traceSegment_067_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 108 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 108 54 54, g32p_row02_traceSegment_067_0108_0054, g32p_row02_traceSegment_067_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 0 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 0 108 108, g32p_row02_traceSegment_067_0000_0108, g32p_row02_traceSegment_067_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 216 13 14, g32p_row02_traceSegment_067_0216_0013, g32p_row02_traceSegment_067_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 243 13 14, g32p_row02_traceSegment_067_0243_0013, g32p_row02_traceSegment_067_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 216 27 27, g32p_row02_traceSegment_067_0216_0027, g32p_row02_traceSegment_067_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 270 13 14, g32p_row02_traceSegment_067_0270_0013, g32p_row02_traceSegment_067_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 297 13 14, g32p_row02_traceSegment_067_0297_0013, g32p_row02_traceSegment_067_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 270 27 27, g32p_row02_traceSegment_067_0270_0027, g32p_row02_traceSegment_067_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 216 54 54, g32p_row02_traceSegment_067_0216_0054, g32p_row02_traceSegment_067_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 324 13 14, g32p_row02_traceSegment_067_0324_0013, g32p_row02_traceSegment_067_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 351 13 14, g32p_row02_traceSegment_067_0351_0013, g32p_row02_traceSegment_067_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 324 27 27, g32p_row02_traceSegment_067_0324_0027, g32p_row02_traceSegment_067_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 378 13 14, g32p_row02_traceSegment_067_0378_0013, g32p_row02_traceSegment_067_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 405 13 14, g32p_row02_traceSegment_067_0405_0013, g32p_row02_traceSegment_067_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 378 27 27, g32p_row02_traceSegment_067_0378_0027, g32p_row02_traceSegment_067_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 324 54 54, g32p_row02_traceSegment_067_0324_0054, g32p_row02_traceSegment_067_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 216 108 108, g32p_row02_traceSegment_067_0216_0108, g32p_row02_traceSegment_067_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_067 0 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 0 216 216, g32p_row02_traceSegment_067_0000_0216, g32p_row02_traceSegment_067_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 432 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 432 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 432 13 14, g32p_row02_traceSegment_067_0432_0013, g32p_row02_traceSegment_067_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 459 13 14, g32p_row02_traceSegment_067_0459_0013, g32p_row02_traceSegment_067_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 432 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 432 27 27, g32p_row02_traceSegment_067_0432_0027, g32p_row02_traceSegment_067_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 486 13 14, g32p_row02_traceSegment_067_0486_0013, g32p_row02_traceSegment_067_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 513 13 14, g32p_row02_traceSegment_067_0513_0013, g32p_row02_traceSegment_067_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 486 27 27, g32p_row02_traceSegment_067_0486_0027, g32p_row02_traceSegment_067_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 432 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 432 54 54, g32p_row02_traceSegment_067_0432_0054, g32p_row02_traceSegment_067_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 540 13 14, g32p_row02_traceSegment_067_0540_0013, g32p_row02_traceSegment_067_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 567 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 567 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 567 13 14, g32p_row02_traceSegment_067_0567_0013, g32p_row02_traceSegment_067_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 540 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 540 27 27, g32p_row02_traceSegment_067_0540_0027, g32p_row02_traceSegment_067_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 594 13 14, g32p_row02_traceSegment_067_0594_0013, g32p_row02_traceSegment_067_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 621 13 14, g32p_row02_traceSegment_067_0621_0013, g32p_row02_traceSegment_067_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 594 27 27, g32p_row02_traceSegment_067_0594_0027, g32p_row02_traceSegment_067_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 540 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 540 54 54, g32p_row02_traceSegment_067_0540_0054, g32p_row02_traceSegment_067_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 432 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 432 108 108, g32p_row02_traceSegment_067_0432_0108, g32p_row02_traceSegment_067_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 648 13 14, g32p_row02_traceSegment_067_0648_0013, g32p_row02_traceSegment_067_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 675 13 14, g32p_row02_traceSegment_067_0675_0013, g32p_row02_traceSegment_067_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 648 27 27, g32p_row02_traceSegment_067_0648_0027, g32p_row02_traceSegment_067_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 702 13 14, g32p_row02_traceSegment_067_0702_0013, g32p_row02_traceSegment_067_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 729 13 14, g32p_row02_traceSegment_067_0729_0013, g32p_row02_traceSegment_067_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 702 27 27, g32p_row02_traceSegment_067_0702_0027, g32p_row02_traceSegment_067_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 648 54 54, g32p_row02_traceSegment_067_0648_0054, g32p_row02_traceSegment_067_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 756 13 14, g32p_row02_traceSegment_067_0756_0013, g32p_row02_traceSegment_067_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 783 13 14, g32p_row02_traceSegment_067_0783_0013, g32p_row02_traceSegment_067_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 756 27 27, g32p_row02_traceSegment_067_0756_0027, g32p_row02_traceSegment_067_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 810 13 14, g32p_row02_traceSegment_067_0810_0013, g32p_row02_traceSegment_067_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 837 13 14, g32p_row02_traceSegment_067_0837_0013, g32p_row02_traceSegment_067_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 810 27 27, g32p_row02_traceSegment_067_0810_0027, g32p_row02_traceSegment_067_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 756 54 54, g32p_row02_traceSegment_067_0756_0054, g32p_row02_traceSegment_067_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 648 108 108, g32p_row02_traceSegment_067_0648_0108, g32p_row02_traceSegment_067_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_067 432 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 432 216 216, g32p_row02_traceSegment_067_0432_0216, g32p_row02_traceSegment_067_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_067 0 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 0 432 432, g32p_row02_traceSegment_067_0000_0432, g32p_row02_traceSegment_067_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 864 13 14, g32p_row02_traceSegment_067_0864_0013, g32p_row02_traceSegment_067_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 891 13 14, g32p_row02_traceSegment_067_0891_0013, g32p_row02_traceSegment_067_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 864 27 27, g32p_row02_traceSegment_067_0864_0027, g32p_row02_traceSegment_067_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 918 13 14, g32p_row02_traceSegment_067_0918_0013, g32p_row02_traceSegment_067_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 945 13 14, g32p_row02_traceSegment_067_0945_0013, g32p_row02_traceSegment_067_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 918 27 27, g32p_row02_traceSegment_067_0918_0027, g32p_row02_traceSegment_067_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 864 54 54, g32p_row02_traceSegment_067_0864_0054, g32p_row02_traceSegment_067_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 972 13 14, g32p_row02_traceSegment_067_0972_0013, g32p_row02_traceSegment_067_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 999 13 14, g32p_row02_traceSegment_067_0999_0013, g32p_row02_traceSegment_067_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 972 27 27, g32p_row02_traceSegment_067_0972_0027, g32p_row02_traceSegment_067_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1026 13 14, g32p_row02_traceSegment_067_1026_0013, g32p_row02_traceSegment_067_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1053 13 14, g32p_row02_traceSegment_067_1053_0013, g32p_row02_traceSegment_067_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1026 27 27, g32p_row02_traceSegment_067_1026_0027, g32p_row02_traceSegment_067_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 972 54 54, g32p_row02_traceSegment_067_0972_0054, g32p_row02_traceSegment_067_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 864 108 108, g32p_row02_traceSegment_067_0864_0108, g32p_row02_traceSegment_067_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1080 13 14, g32p_row02_traceSegment_067_1080_0013, g32p_row02_traceSegment_067_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1107 13 14, g32p_row02_traceSegment_067_1107_0013, g32p_row02_traceSegment_067_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1080 27 27, g32p_row02_traceSegment_067_1080_0027, g32p_row02_traceSegment_067_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1134 13 14, g32p_row02_traceSegment_067_1134_0013, g32p_row02_traceSegment_067_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1161 13 14, g32p_row02_traceSegment_067_1161_0013, g32p_row02_traceSegment_067_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1134 27 27, g32p_row02_traceSegment_067_1134_0027, g32p_row02_traceSegment_067_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1080 54 54, g32p_row02_traceSegment_067_1080_0054, g32p_row02_traceSegment_067_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1188 13 14, g32p_row02_traceSegment_067_1188_0013, g32p_row02_traceSegment_067_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1215 13 14, g32p_row02_traceSegment_067_1215_0013, g32p_row02_traceSegment_067_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1188 27 27, g32p_row02_traceSegment_067_1188_0027, g32p_row02_traceSegment_067_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1242 13 14, g32p_row02_traceSegment_067_1242_0013, g32p_row02_traceSegment_067_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1269 13 14, g32p_row02_traceSegment_067_1269_0013, g32p_row02_traceSegment_067_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1242 27 27, g32p_row02_traceSegment_067_1242_0027, g32p_row02_traceSegment_067_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1188 54 54, g32p_row02_traceSegment_067_1188_0054, g32p_row02_traceSegment_067_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1080 108 108, g32p_row02_traceSegment_067_1080_0108, g32p_row02_traceSegment_067_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_067 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 864 216 216, g32p_row02_traceSegment_067_0864_0216, g32p_row02_traceSegment_067_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1296 13 14, g32p_row02_traceSegment_067_1296_0013, g32p_row02_traceSegment_067_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1323 13 14, g32p_row02_traceSegment_067_1323_0013, g32p_row02_traceSegment_067_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1296 27 27, g32p_row02_traceSegment_067_1296_0027, g32p_row02_traceSegment_067_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1350 13 14, g32p_row02_traceSegment_067_1350_0013, g32p_row02_traceSegment_067_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1377 13 14, g32p_row02_traceSegment_067_1377_0013, g32p_row02_traceSegment_067_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1350 27 27, g32p_row02_traceSegment_067_1350_0027, g32p_row02_traceSegment_067_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1296 54 54, g32p_row02_traceSegment_067_1296_0054, g32p_row02_traceSegment_067_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1404 13 14, g32p_row02_traceSegment_067_1404_0013, g32p_row02_traceSegment_067_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1431 13 14, g32p_row02_traceSegment_067_1431_0013, g32p_row02_traceSegment_067_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1404 27 27, g32p_row02_traceSegment_067_1404_0027, g32p_row02_traceSegment_067_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1458 13 14, g32p_row02_traceSegment_067_1458_0013, g32p_row02_traceSegment_067_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1485 13 14, g32p_row02_traceSegment_067_1485_0013, g32p_row02_traceSegment_067_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1458 27 27, g32p_row02_traceSegment_067_1458_0027, g32p_row02_traceSegment_067_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1404 54 54, g32p_row02_traceSegment_067_1404_0054, g32p_row02_traceSegment_067_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1296 108 108, g32p_row02_traceSegment_067_1296_0108, g32p_row02_traceSegment_067_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1512 13 14, g32p_row02_traceSegment_067_1512_0013, g32p_row02_traceSegment_067_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1539 13 14, g32p_row02_traceSegment_067_1539_0013, g32p_row02_traceSegment_067_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1512 27 27, g32p_row02_traceSegment_067_1512_0027, g32p_row02_traceSegment_067_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1566 13 14, g32p_row02_traceSegment_067_1566_0013, g32p_row02_traceSegment_067_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1593 13 14, g32p_row02_traceSegment_067_1593_0013, g32p_row02_traceSegment_067_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1566 27 27, g32p_row02_traceSegment_067_1566_0027, g32p_row02_traceSegment_067_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1512 54 54, g32p_row02_traceSegment_067_1512_0054, g32p_row02_traceSegment_067_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1620 13 14, g32p_row02_traceSegment_067_1620_0013, g32p_row02_traceSegment_067_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1647 13 14, g32p_row02_traceSegment_067_1647_0013, g32p_row02_traceSegment_067_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1620 27 27, g32p_row02_traceSegment_067_1620_0027, g32p_row02_traceSegment_067_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1674 13 14, g32p_row02_traceSegment_067_1674_0013, g32p_row02_traceSegment_067_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1701 13 14, g32p_row02_traceSegment_067_1701_0013, g32p_row02_traceSegment_067_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1674 27 27, g32p_row02_traceSegment_067_1674_0027, g32p_row02_traceSegment_067_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1620 54 54, g32p_row02_traceSegment_067_1620_0054, g32p_row02_traceSegment_067_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1512 108 108, g32p_row02_traceSegment_067_1512_0108, g32p_row02_traceSegment_067_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_067 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1296 216 216, g32p_row02_traceSegment_067_1296_0216, g32p_row02_traceSegment_067_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_067 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 864 432 432, g32p_row02_traceSegment_067_0864_0432, g32p_row02_traceSegment_067_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_067 0 1728 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 0 864 864, g32p_row02_traceSegment_067_0000_0864, g32p_row02_traceSegment_067_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1728 13 14, g32p_row02_traceSegment_067_1728_0013, g32p_row02_traceSegment_067_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1755 13 14, g32p_row02_traceSegment_067_1755_0013, g32p_row02_traceSegment_067_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1728 27 27, g32p_row02_traceSegment_067_1728_0027, g32p_row02_traceSegment_067_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1782 13 14, g32p_row02_traceSegment_067_1782_0013, g32p_row02_traceSegment_067_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1809 13 14, g32p_row02_traceSegment_067_1809_0013, g32p_row02_traceSegment_067_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1782 27 27, g32p_row02_traceSegment_067_1782_0027, g32p_row02_traceSegment_067_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1728 54 54, g32p_row02_traceSegment_067_1728_0054, g32p_row02_traceSegment_067_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1836 13 14, g32p_row02_traceSegment_067_1836_0013, g32p_row02_traceSegment_067_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1863 13 14, g32p_row02_traceSegment_067_1863_0013, g32p_row02_traceSegment_067_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1836 27 27, g32p_row02_traceSegment_067_1836_0027, g32p_row02_traceSegment_067_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1903 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1890 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1890 13 14, g32p_row02_traceSegment_067_1890_0013, g32p_row02_traceSegment_067_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1917 13 14, g32p_row02_traceSegment_067_1917_0013, g32p_row02_traceSegment_067_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1890 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1890 27 27, g32p_row02_traceSegment_067_1890_0027, g32p_row02_traceSegment_067_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 1836 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1836 54 54, g32p_row02_traceSegment_067_1836_0054, g32p_row02_traceSegment_067_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 1728 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1728 108 108, g32p_row02_traceSegment_067_1728_0108, g32p_row02_traceSegment_067_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1944 13 14, g32p_row02_traceSegment_067_1944_0013, g32p_row02_traceSegment_067_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1971 13 14, g32p_row02_traceSegment_067_1971_0013, g32p_row02_traceSegment_067_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1944 27 27, g32p_row02_traceSegment_067_1944_0027, g32p_row02_traceSegment_067_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1998 13 14, g32p_row02_traceSegment_067_1998_0013, g32p_row02_traceSegment_067_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2025 13 14, g32p_row02_traceSegment_067_2025_0013, g32p_row02_traceSegment_067_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1998 27 27, g32p_row02_traceSegment_067_1998_0027, g32p_row02_traceSegment_067_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1944 54 54, g32p_row02_traceSegment_067_1944_0054, g32p_row02_traceSegment_067_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2052 13 14, g32p_row02_traceSegment_067_2052_0013, g32p_row02_traceSegment_067_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2079 13 14, g32p_row02_traceSegment_067_2079_0013, g32p_row02_traceSegment_067_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2052 27 27, g32p_row02_traceSegment_067_2052_0027, g32p_row02_traceSegment_067_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2106 13 14, g32p_row02_traceSegment_067_2106_0013, g32p_row02_traceSegment_067_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2133 13 14, g32p_row02_traceSegment_067_2133_0013, g32p_row02_traceSegment_067_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2106 27 27, g32p_row02_traceSegment_067_2106_0027, g32p_row02_traceSegment_067_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2052 54 54, g32p_row02_traceSegment_067_2052_0054, g32p_row02_traceSegment_067_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1944 108 108, g32p_row02_traceSegment_067_1944_0108, g32p_row02_traceSegment_067_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_067 1728 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1728 216 216, g32p_row02_traceSegment_067_1728_0216, g32p_row02_traceSegment_067_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2160 13 14, g32p_row02_traceSegment_067_2160_0013, g32p_row02_traceSegment_067_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2187 13 14, g32p_row02_traceSegment_067_2187_0013, g32p_row02_traceSegment_067_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2160 27 27, g32p_row02_traceSegment_067_2160_0027, g32p_row02_traceSegment_067_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2214 13 14, g32p_row02_traceSegment_067_2214_0013, g32p_row02_traceSegment_067_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2241 13 14, g32p_row02_traceSegment_067_2241_0013, g32p_row02_traceSegment_067_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2214 27 27, g32p_row02_traceSegment_067_2214_0027, g32p_row02_traceSegment_067_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2160 54 54, g32p_row02_traceSegment_067_2160_0054, g32p_row02_traceSegment_067_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2268 13 14, g32p_row02_traceSegment_067_2268_0013, g32p_row02_traceSegment_067_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2295 13 14, g32p_row02_traceSegment_067_2295_0013, g32p_row02_traceSegment_067_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2268 27 27, g32p_row02_traceSegment_067_2268_0027, g32p_row02_traceSegment_067_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2322 13 14, g32p_row02_traceSegment_067_2322_0013, g32p_row02_traceSegment_067_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2349 13 14, g32p_row02_traceSegment_067_2349_0013, g32p_row02_traceSegment_067_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2322 27 27, g32p_row02_traceSegment_067_2322_0027, g32p_row02_traceSegment_067_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2268 54 54, g32p_row02_traceSegment_067_2268_0054, g32p_row02_traceSegment_067_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2160 108 108, g32p_row02_traceSegment_067_2160_0108, g32p_row02_traceSegment_067_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2376 13 14, g32p_row02_traceSegment_067_2376_0013, g32p_row02_traceSegment_067_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2403 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2403 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2403 13 14, g32p_row02_traceSegment_067_2403_0013, g32p_row02_traceSegment_067_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2376 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2376 27 27, g32p_row02_traceSegment_067_2376_0027, g32p_row02_traceSegment_067_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2430 13 14, g32p_row02_traceSegment_067_2430_0013, g32p_row02_traceSegment_067_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2457 13 14, g32p_row02_traceSegment_067_2457_0013, g32p_row02_traceSegment_067_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2430 27 27, g32p_row02_traceSegment_067_2430_0027, g32p_row02_traceSegment_067_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 2376 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2376 54 54, g32p_row02_traceSegment_067_2376_0054, g32p_row02_traceSegment_067_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2484 13 14, g32p_row02_traceSegment_067_2484_0013, g32p_row02_traceSegment_067_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2511 13 14, g32p_row02_traceSegment_067_2511_0013, g32p_row02_traceSegment_067_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2484 27 27, g32p_row02_traceSegment_067_2484_0027, g32p_row02_traceSegment_067_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2538 13 14, g32p_row02_traceSegment_067_2538_0013, g32p_row02_traceSegment_067_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2565 13 14, g32p_row02_traceSegment_067_2565_0013, g32p_row02_traceSegment_067_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2538 27 27, g32p_row02_traceSegment_067_2538_0027, g32p_row02_traceSegment_067_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2484 54 54, g32p_row02_traceSegment_067_2484_0054, g32p_row02_traceSegment_067_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 2376 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2376 108 108, g32p_row02_traceSegment_067_2376_0108, g32p_row02_traceSegment_067_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_067 2160 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2160 216 216, g32p_row02_traceSegment_067_2160_0216, g32p_row02_traceSegment_067_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_067 1728 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1728 432 432, g32p_row02_traceSegment_067_1728_0432, g32p_row02_traceSegment_067_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2592 13 14, g32p_row02_traceSegment_067_2592_0013, g32p_row02_traceSegment_067_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2619 13 14, g32p_row02_traceSegment_067_2619_0013, g32p_row02_traceSegment_067_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2592 27 27, g32p_row02_traceSegment_067_2592_0027, g32p_row02_traceSegment_067_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2646 13 14, g32p_row02_traceSegment_067_2646_0013, g32p_row02_traceSegment_067_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2673 13 14, g32p_row02_traceSegment_067_2673_0013, g32p_row02_traceSegment_067_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2646 27 27, g32p_row02_traceSegment_067_2646_0027, g32p_row02_traceSegment_067_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2592 54 54, g32p_row02_traceSegment_067_2592_0054, g32p_row02_traceSegment_067_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2700 13 14, g32p_row02_traceSegment_067_2700_0013, g32p_row02_traceSegment_067_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2727 13 14, g32p_row02_traceSegment_067_2727_0013, g32p_row02_traceSegment_067_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2700 27 27, g32p_row02_traceSegment_067_2700_0027, g32p_row02_traceSegment_067_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2754 13 14, g32p_row02_traceSegment_067_2754_0013, g32p_row02_traceSegment_067_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2781 13 14, g32p_row02_traceSegment_067_2781_0013, g32p_row02_traceSegment_067_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2754 27 27, g32p_row02_traceSegment_067_2754_0027, g32p_row02_traceSegment_067_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2700 54 54, g32p_row02_traceSegment_067_2700_0054, g32p_row02_traceSegment_067_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2592 108 108, g32p_row02_traceSegment_067_2592_0108, g32p_row02_traceSegment_067_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2808 13 14, g32p_row02_traceSegment_067_2808_0013, g32p_row02_traceSegment_067_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2835 13 14, g32p_row02_traceSegment_067_2835_0013, g32p_row02_traceSegment_067_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2808 27 27, g32p_row02_traceSegment_067_2808_0027, g32p_row02_traceSegment_067_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2862 13 14, g32p_row02_traceSegment_067_2862_0013, g32p_row02_traceSegment_067_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2889 13 14, g32p_row02_traceSegment_067_2889_0013, g32p_row02_traceSegment_067_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2862 27 27, g32p_row02_traceSegment_067_2862_0027, g32p_row02_traceSegment_067_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2808 54 54, g32p_row02_traceSegment_067_2808_0054, g32p_row02_traceSegment_067_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2916 13 14, g32p_row02_traceSegment_067_2916_0013, g32p_row02_traceSegment_067_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2943 13 14, g32p_row02_traceSegment_067_2943_0013, g32p_row02_traceSegment_067_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2916 27 27, g32p_row02_traceSegment_067_2916_0027, g32p_row02_traceSegment_067_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2970 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2970 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2970 13 14, g32p_row02_traceSegment_067_2970_0013, g32p_row02_traceSegment_067_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 2997 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 2997 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2997 13 14, g32p_row02_traceSegment_067_2997_0013, g32p_row02_traceSegment_067_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 2970 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2970 27 27, g32p_row02_traceSegment_067_2970_0027, g32p_row02_traceSegment_067_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 2916 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2916 54 54, g32p_row02_traceSegment_067_2916_0054, g32p_row02_traceSegment_067_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 2808 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2808 108 108, g32p_row02_traceSegment_067_2808_0108, g32p_row02_traceSegment_067_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_067 2592 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2592 216 216, g32p_row02_traceSegment_067_2592_0216, g32p_row02_traceSegment_067_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3024 13 14, g32p_row02_traceSegment_067_3024_0013, g32p_row02_traceSegment_067_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3051 13 14, g32p_row02_traceSegment_067_3051_0013, g32p_row02_traceSegment_067_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3024 27 27, g32p_row02_traceSegment_067_3024_0027, g32p_row02_traceSegment_067_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3078 13 14, g32p_row02_traceSegment_067_3078_0013, g32p_row02_traceSegment_067_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3105 13 14, g32p_row02_traceSegment_067_3105_0013, g32p_row02_traceSegment_067_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3078 27 27, g32p_row02_traceSegment_067_3078_0027, g32p_row02_traceSegment_067_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3024 54 54, g32p_row02_traceSegment_067_3024_0054, g32p_row02_traceSegment_067_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3132 13 14, g32p_row02_traceSegment_067_3132_0013, g32p_row02_traceSegment_067_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3159 13 14, g32p_row02_traceSegment_067_3159_0013, g32p_row02_traceSegment_067_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3132 27 27, g32p_row02_traceSegment_067_3132_0027, g32p_row02_traceSegment_067_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3186 13 14, g32p_row02_traceSegment_067_3186_0013, g32p_row02_traceSegment_067_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3213 13 14, g32p_row02_traceSegment_067_3213_0013, g32p_row02_traceSegment_067_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3186 27 27, g32p_row02_traceSegment_067_3186_0027, g32p_row02_traceSegment_067_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3132 54 54, g32p_row02_traceSegment_067_3132_0054, g32p_row02_traceSegment_067_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3024 108 108, g32p_row02_traceSegment_067_3024_0108, g32p_row02_traceSegment_067_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3240 13 14, g32p_row02_traceSegment_067_3240_0013, g32p_row02_traceSegment_067_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3267 13 14, g32p_row02_traceSegment_067_3267_0013, g32p_row02_traceSegment_067_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3240 27 27, g32p_row02_traceSegment_067_3240_0027, g32p_row02_traceSegment_067_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3294 13 14, g32p_row02_traceSegment_067_3294_0013, g32p_row02_traceSegment_067_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3321 13 14, g32p_row02_traceSegment_067_3321_0013, g32p_row02_traceSegment_067_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3294 27 27, g32p_row02_traceSegment_067_3294_0027, g32p_row02_traceSegment_067_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3240 54 54, g32p_row02_traceSegment_067_3240_0054, g32p_row02_traceSegment_067_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3348 13 14, g32p_row02_traceSegment_067_3348_0013, g32p_row02_traceSegment_067_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3375 13 14, g32p_row02_traceSegment_067_3375_0013, g32p_row02_traceSegment_067_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3348 27 27, g32p_row02_traceSegment_067_3348_0027, g32p_row02_traceSegment_067_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3402 13 14, g32p_row02_traceSegment_067_3402_0013, g32p_row02_traceSegment_067_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_067 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_067 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_067_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_067 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3429 13 14, g32p_row02_traceSegment_067_3429_0013, g32p_row02_traceSegment_067_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_067 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3402 27 27, g32p_row02_traceSegment_067_3402_0027, g32p_row02_traceSegment_067_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_067 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3348 54 54, g32p_row02_traceSegment_067_3348_0054, g32p_row02_traceSegment_067_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_067 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3240 108 108, g32p_row02_traceSegment_067_3240_0108, g32p_row02_traceSegment_067_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_067_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_067 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 3024 216 216, g32p_row02_traceSegment_067_3024_0216, g32p_row02_traceSegment_067_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_067_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_067 2592 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 2592 432 432, g32p_row02_traceSegment_067_2592_0432, g32p_row02_traceSegment_067_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_067_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_067 1728 1728 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 1728 864 864, g32p_row02_traceSegment_067_1728_0864, g32p_row02_traceSegment_067_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_067_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_067 0 3456 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_067 0 1728 1728, g32p_row02_traceSegment_067_0000_1728, g32p_row02_traceSegment_067_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 67 = [0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_067_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_069 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 69 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_069_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 0 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 13 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 0 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 0 13 14, g32p_row02_traceSegment_069_0000_0013, g32p_row02_traceSegment_069_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 27 13 14, g32p_row02_traceSegment_069_0027_0013, g32p_row02_traceSegment_069_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 0 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 0 27 27, g32p_row02_traceSegment_069_0000_0027, g32p_row02_traceSegment_069_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 54 13 14, g32p_row02_traceSegment_069_0054_0013, g32p_row02_traceSegment_069_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 81 13 14, g32p_row02_traceSegment_069_0081_0013, g32p_row02_traceSegment_069_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 54 27 27, g32p_row02_traceSegment_069_0054_0027, g32p_row02_traceSegment_069_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 0 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 0 54 54, g32p_row02_traceSegment_069_0000_0054, g32p_row02_traceSegment_069_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 108 13 14, g32p_row02_traceSegment_069_0108_0013, g32p_row02_traceSegment_069_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 135 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 148 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 135 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 135 13 14, g32p_row02_traceSegment_069_0135_0013, g32p_row02_traceSegment_069_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 108 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 108 27 27, g32p_row02_traceSegment_069_0108_0027, g32p_row02_traceSegment_069_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 162 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 175 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 162 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 162 13 14, g32p_row02_traceSegment_069_0162_0013, g32p_row02_traceSegment_069_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 189 13 14, g32p_row02_traceSegment_069_0189_0013, g32p_row02_traceSegment_069_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 162 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 162 27 27, g32p_row02_traceSegment_069_0162_0027, g32p_row02_traceSegment_069_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 108 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 108 54 54, g32p_row02_traceSegment_069_0108_0054, g32p_row02_traceSegment_069_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 0 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 0 108 108, g32p_row02_traceSegment_069_0000_0108, g32p_row02_traceSegment_069_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 216 13 14, g32p_row02_traceSegment_069_0216_0013, g32p_row02_traceSegment_069_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 243 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 243 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 243 13 14, g32p_row02_traceSegment_069_0243_0013, g32p_row02_traceSegment_069_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 216 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 216 27 27, g32p_row02_traceSegment_069_0216_0027, g32p_row02_traceSegment_069_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 270 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 270 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 270 13 14, g32p_row02_traceSegment_069_0270_0013, g32p_row02_traceSegment_069_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 297 13 14, g32p_row02_traceSegment_069_0297_0013, g32p_row02_traceSegment_069_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 270 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 270 27 27, g32p_row02_traceSegment_069_0270_0027, g32p_row02_traceSegment_069_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 216 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 216 54 54, g32p_row02_traceSegment_069_0216_0054, g32p_row02_traceSegment_069_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 337 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 324 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 324 13 14, g32p_row02_traceSegment_069_0324_0013, g32p_row02_traceSegment_069_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 351 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 351 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 351 13 14, g32p_row02_traceSegment_069_0351_0013, g32p_row02_traceSegment_069_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 324 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 324 27 27, g32p_row02_traceSegment_069_0324_0027, g32p_row02_traceSegment_069_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 391 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 378 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 378 13 14, g32p_row02_traceSegment_069_0378_0013, g32p_row02_traceSegment_069_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 405 13 14, g32p_row02_traceSegment_069_0405_0013, g32p_row02_traceSegment_069_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 378 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 378 27 27, g32p_row02_traceSegment_069_0378_0027, g32p_row02_traceSegment_069_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 324 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 324 54 54, g32p_row02_traceSegment_069_0324_0054, g32p_row02_traceSegment_069_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 216 216 = [7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 216 108 108, g32p_row02_traceSegment_069_0216_0108, g32p_row02_traceSegment_069_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_069 0 432 = [13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 0 216 216, g32p_row02_traceSegment_069_0000_0216, g32p_row02_traceSegment_069_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 432 13 14, g32p_row02_traceSegment_069_0432_0013, g32p_row02_traceSegment_069_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 459 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 459 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 459 13 14, g32p_row02_traceSegment_069_0459_0013, g32p_row02_traceSegment_069_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 432 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 432 27 27, g32p_row02_traceSegment_069_0432_0027, g32p_row02_traceSegment_069_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 486 13 14, g32p_row02_traceSegment_069_0486_0013, g32p_row02_traceSegment_069_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 513 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 526 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 513 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 513 13 14, g32p_row02_traceSegment_069_0513_0013, g32p_row02_traceSegment_069_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 486 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 486 27 27, g32p_row02_traceSegment_069_0486_0027, g32p_row02_traceSegment_069_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 432 108 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 432 54 54, g32p_row02_traceSegment_069_0432_0054, g32p_row02_traceSegment_069_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 540 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 553 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 540 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 540 13 14, g32p_row02_traceSegment_069_0540_0013, g32p_row02_traceSegment_069_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 567 13 14, g32p_row02_traceSegment_069_0567_0013, g32p_row02_traceSegment_069_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 540 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 540 27 27, g32p_row02_traceSegment_069_0540_0027, g32p_row02_traceSegment_069_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 594 13 14, g32p_row02_traceSegment_069_0594_0013, g32p_row02_traceSegment_069_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 621 13 14, g32p_row02_traceSegment_069_0621_0013, g32p_row02_traceSegment_069_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 594 27 27, g32p_row02_traceSegment_069_0594_0027, g32p_row02_traceSegment_069_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 540 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 540 54 54, g32p_row02_traceSegment_069_0540_0054, g32p_row02_traceSegment_069_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 432 216 = [2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 432 108 108, g32p_row02_traceSegment_069_0432_0108, g32p_row02_traceSegment_069_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 648 13 14, g32p_row02_traceSegment_069_0648_0013, g32p_row02_traceSegment_069_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 688 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 675 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 675 13 14, g32p_row02_traceSegment_069_0675_0013, g32p_row02_traceSegment_069_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 648 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 648 27 27, g32p_row02_traceSegment_069_0648_0027, g32p_row02_traceSegment_069_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 702 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 702 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 702 13 14, g32p_row02_traceSegment_069_0702_0013, g32p_row02_traceSegment_069_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 729 13 14, g32p_row02_traceSegment_069_0729_0013, g32p_row02_traceSegment_069_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 702 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 702 27 27, g32p_row02_traceSegment_069_0702_0027, g32p_row02_traceSegment_069_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 648 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 648 54 54, g32p_row02_traceSegment_069_0648_0054, g32p_row02_traceSegment_069_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 756 13 14, g32p_row02_traceSegment_069_0756_0013, g32p_row02_traceSegment_069_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 783 13 14, g32p_row02_traceSegment_069_0783_0013, g32p_row02_traceSegment_069_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 756 27 27, g32p_row02_traceSegment_069_0756_0027, g32p_row02_traceSegment_069_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 810 13 14, g32p_row02_traceSegment_069_0810_0013, g32p_row02_traceSegment_069_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 837 13 14, g32p_row02_traceSegment_069_0837_0013, g32p_row02_traceSegment_069_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 810 27 27, g32p_row02_traceSegment_069_0810_0027, g32p_row02_traceSegment_069_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 756 54 54, g32p_row02_traceSegment_069_0756_0054, g32p_row02_traceSegment_069_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 648 216 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 648 108 108, g32p_row02_traceSegment_069_0648_0108, g32p_row02_traceSegment_069_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_069 432 432 = [2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 432 216 216, g32p_row02_traceSegment_069_0432_0216, g32p_row02_traceSegment_069_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_069 0 864 = [15, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 0 432 432, g32p_row02_traceSegment_069_0000_0432, g32p_row02_traceSegment_069_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 864 13 14, g32p_row02_traceSegment_069_0864_0013, g32p_row02_traceSegment_069_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 891 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 891 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 891 13 14, g32p_row02_traceSegment_069_0891_0013, g32p_row02_traceSegment_069_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 864 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 864 27 27, g32p_row02_traceSegment_069_0864_0027, g32p_row02_traceSegment_069_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 918 13 14, g32p_row02_traceSegment_069_0918_0013, g32p_row02_traceSegment_069_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 945 13 14, g32p_row02_traceSegment_069_0945_0013, g32p_row02_traceSegment_069_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 918 27 27, g32p_row02_traceSegment_069_0918_0027, g32p_row02_traceSegment_069_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 864 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 864 54 54, g32p_row02_traceSegment_069_0864_0054, g32p_row02_traceSegment_069_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 972 13 14, g32p_row02_traceSegment_069_0972_0013, g32p_row02_traceSegment_069_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 999 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1012 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 999 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 999 13 14, g32p_row02_traceSegment_069_0999_0013, g32p_row02_traceSegment_069_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 972 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 972 27 27, g32p_row02_traceSegment_069_0972_0027, g32p_row02_traceSegment_069_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1026 13 14, g32p_row02_traceSegment_069_1026_0013, g32p_row02_traceSegment_069_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1053 13 14, g32p_row02_traceSegment_069_1053_0013, g32p_row02_traceSegment_069_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1026 27 27, g32p_row02_traceSegment_069_1026_0027, g32p_row02_traceSegment_069_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 972 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 972 54 54, g32p_row02_traceSegment_069_0972_0054, g32p_row02_traceSegment_069_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 864 216 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 864 108 108, g32p_row02_traceSegment_069_0864_0108, g32p_row02_traceSegment_069_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1080 13 14, g32p_row02_traceSegment_069_1080_0013, g32p_row02_traceSegment_069_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1107 13 14, g32p_row02_traceSegment_069_1107_0013, g32p_row02_traceSegment_069_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1080 27 27, g32p_row02_traceSegment_069_1080_0027, g32p_row02_traceSegment_069_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1134 13 14, g32p_row02_traceSegment_069_1134_0013, g32p_row02_traceSegment_069_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1161 13 14, g32p_row02_traceSegment_069_1161_0013, g32p_row02_traceSegment_069_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1134 27 27, g32p_row02_traceSegment_069_1134_0027, g32p_row02_traceSegment_069_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1080 54 54, g32p_row02_traceSegment_069_1080_0054, g32p_row02_traceSegment_069_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1188 13 14, g32p_row02_traceSegment_069_1188_0013, g32p_row02_traceSegment_069_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1215 13 14, g32p_row02_traceSegment_069_1215_0013, g32p_row02_traceSegment_069_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1188 27 27, g32p_row02_traceSegment_069_1188_0027, g32p_row02_traceSegment_069_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1242 13 14, g32p_row02_traceSegment_069_1242_0013, g32p_row02_traceSegment_069_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1269 13 14, g32p_row02_traceSegment_069_1269_0013, g32p_row02_traceSegment_069_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1242 27 27, g32p_row02_traceSegment_069_1242_0027, g32p_row02_traceSegment_069_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1188 54 54, g32p_row02_traceSegment_069_1188_0054, g32p_row02_traceSegment_069_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1080 108 108, g32p_row02_traceSegment_069_1080_0108, g32p_row02_traceSegment_069_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_069 864 432 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 864 216 216, g32p_row02_traceSegment_069_0864_0216, g32p_row02_traceSegment_069_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1296 13 14, g32p_row02_traceSegment_069_1296_0013, g32p_row02_traceSegment_069_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1323 13 14, g32p_row02_traceSegment_069_1323_0013, g32p_row02_traceSegment_069_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1296 27 27, g32p_row02_traceSegment_069_1296_0027, g32p_row02_traceSegment_069_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1350 13 14, g32p_row02_traceSegment_069_1350_0013, g32p_row02_traceSegment_069_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1377 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1377 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1377 13 14, g32p_row02_traceSegment_069_1377_0013, g32p_row02_traceSegment_069_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1350 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1350 27 27, g32p_row02_traceSegment_069_1350_0027, g32p_row02_traceSegment_069_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 1296 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1296 54 54, g32p_row02_traceSegment_069_1296_0054, g32p_row02_traceSegment_069_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1417 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1404 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1404 13 14, g32p_row02_traceSegment_069_1404_0013, g32p_row02_traceSegment_069_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1431 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1431 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1431 13 14, g32p_row02_traceSegment_069_1431_0013, g32p_row02_traceSegment_069_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1404 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1404 27 27, g32p_row02_traceSegment_069_1404_0027, g32p_row02_traceSegment_069_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1458 13 14, g32p_row02_traceSegment_069_1458_0013, g32p_row02_traceSegment_069_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1485 13 14, g32p_row02_traceSegment_069_1485_0013, g32p_row02_traceSegment_069_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1458 27 27, g32p_row02_traceSegment_069_1458_0027, g32p_row02_traceSegment_069_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 1404 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1404 54 54, g32p_row02_traceSegment_069_1404_0054, g32p_row02_traceSegment_069_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 1296 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1296 108 108, g32p_row02_traceSegment_069_1296_0108, g32p_row02_traceSegment_069_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1512 13 14, g32p_row02_traceSegment_069_1512_0013, g32p_row02_traceSegment_069_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1539 13 14, g32p_row02_traceSegment_069_1539_0013, g32p_row02_traceSegment_069_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1512 27 27, g32p_row02_traceSegment_069_1512_0027, g32p_row02_traceSegment_069_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1566 13 14, g32p_row02_traceSegment_069_1566_0013, g32p_row02_traceSegment_069_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1593 13 14, g32p_row02_traceSegment_069_1593_0013, g32p_row02_traceSegment_069_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1566 27 27, g32p_row02_traceSegment_069_1566_0027, g32p_row02_traceSegment_069_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1512 54 54, g32p_row02_traceSegment_069_1512_0054, g32p_row02_traceSegment_069_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1620 13 14, g32p_row02_traceSegment_069_1620_0013, g32p_row02_traceSegment_069_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1647 13 14, g32p_row02_traceSegment_069_1647_0013, g32p_row02_traceSegment_069_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1620 27 27, g32p_row02_traceSegment_069_1620_0027, g32p_row02_traceSegment_069_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1674 13 14, g32p_row02_traceSegment_069_1674_0013, g32p_row02_traceSegment_069_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1701 13 14, g32p_row02_traceSegment_069_1701_0013, g32p_row02_traceSegment_069_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1674 27 27, g32p_row02_traceSegment_069_1674_0027, g32p_row02_traceSegment_069_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1620 54 54, g32p_row02_traceSegment_069_1620_0054, g32p_row02_traceSegment_069_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1512 108 108, g32p_row02_traceSegment_069_1512_0108, g32p_row02_traceSegment_069_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_069 1296 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1296 216 216, g32p_row02_traceSegment_069_1296_0216, g32p_row02_traceSegment_069_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_069 864 864 = [5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 864 432 432, g32p_row02_traceSegment_069_0864_0432, g32p_row02_traceSegment_069_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_069 0 1728 = [20, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 0 864 864, g32p_row02_traceSegment_069_0000_0864, g32p_row02_traceSegment_069_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1728 13 14, g32p_row02_traceSegment_069_1728_0013, g32p_row02_traceSegment_069_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1755 13 14, g32p_row02_traceSegment_069_1755_0013, g32p_row02_traceSegment_069_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1728 27 27, g32p_row02_traceSegment_069_1728_0027, g32p_row02_traceSegment_069_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1782 13 14, g32p_row02_traceSegment_069_1782_0013, g32p_row02_traceSegment_069_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1809 13 14, g32p_row02_traceSegment_069_1809_0013, g32p_row02_traceSegment_069_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1782 27 27, g32p_row02_traceSegment_069_1782_0027, g32p_row02_traceSegment_069_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1728 54 54, g32p_row02_traceSegment_069_1728_0054, g32p_row02_traceSegment_069_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1836 13 14, g32p_row02_traceSegment_069_1836_0013, g32p_row02_traceSegment_069_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1863 13 14, g32p_row02_traceSegment_069_1863_0013, g32p_row02_traceSegment_069_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1836 27 27, g32p_row02_traceSegment_069_1836_0027, g32p_row02_traceSegment_069_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1890 13 14, g32p_row02_traceSegment_069_1890_0013, g32p_row02_traceSegment_069_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1917 13 14, g32p_row02_traceSegment_069_1917_0013, g32p_row02_traceSegment_069_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1890 27 27, g32p_row02_traceSegment_069_1890_0027, g32p_row02_traceSegment_069_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1836 54 54, g32p_row02_traceSegment_069_1836_0054, g32p_row02_traceSegment_069_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1728 108 108, g32p_row02_traceSegment_069_1728_0108, g32p_row02_traceSegment_069_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1944 13 14, g32p_row02_traceSegment_069_1944_0013, g32p_row02_traceSegment_069_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1971 13 14, g32p_row02_traceSegment_069_1971_0013, g32p_row02_traceSegment_069_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1944 27 27, g32p_row02_traceSegment_069_1944_0027, g32p_row02_traceSegment_069_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1998 13 14, g32p_row02_traceSegment_069_1998_0013, g32p_row02_traceSegment_069_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2025 13 14, g32p_row02_traceSegment_069_2025_0013, g32p_row02_traceSegment_069_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1998 27 27, g32p_row02_traceSegment_069_1998_0027, g32p_row02_traceSegment_069_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1944 54 54, g32p_row02_traceSegment_069_1944_0054, g32p_row02_traceSegment_069_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2052 13 14, g32p_row02_traceSegment_069_2052_0013, g32p_row02_traceSegment_069_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2079 13 14, g32p_row02_traceSegment_069_2079_0013, g32p_row02_traceSegment_069_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2052 27 27, g32p_row02_traceSegment_069_2052_0027, g32p_row02_traceSegment_069_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2106 13 14, g32p_row02_traceSegment_069_2106_0013, g32p_row02_traceSegment_069_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2133 13 14, g32p_row02_traceSegment_069_2133_0013, g32p_row02_traceSegment_069_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2106 27 27, g32p_row02_traceSegment_069_2106_0027, g32p_row02_traceSegment_069_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2052 54 54, g32p_row02_traceSegment_069_2052_0054, g32p_row02_traceSegment_069_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1944 108 108, g32p_row02_traceSegment_069_1944_0108, g32p_row02_traceSegment_069_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_069 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1728 216 216, g32p_row02_traceSegment_069_1728_0216, g32p_row02_traceSegment_069_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2160 13 14, g32p_row02_traceSegment_069_2160_0013, g32p_row02_traceSegment_069_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2187 13 14, g32p_row02_traceSegment_069_2187_0013, g32p_row02_traceSegment_069_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2160 27 27, g32p_row02_traceSegment_069_2160_0027, g32p_row02_traceSegment_069_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2214 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2214 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2214 13 14, g32p_row02_traceSegment_069_2214_0013, g32p_row02_traceSegment_069_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2254 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2241 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2241 13 14, g32p_row02_traceSegment_069_2241_0013, g32p_row02_traceSegment_069_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2214 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2214 27 27, g32p_row02_traceSegment_069_2214_0027, g32p_row02_traceSegment_069_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 2160 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2160 54 54, g32p_row02_traceSegment_069_2160_0054, g32p_row02_traceSegment_069_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2268 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2268 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2268 13 14, g32p_row02_traceSegment_069_2268_0013, g32p_row02_traceSegment_069_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2295 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2308 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2295 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2295 13 14, g32p_row02_traceSegment_069_2295_0013, g32p_row02_traceSegment_069_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2268 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2268 27 27, g32p_row02_traceSegment_069_2268_0027, g32p_row02_traceSegment_069_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2322 13 = [3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2322 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2322 13 14, g32p_row02_traceSegment_069_2322_0013, g32p_row02_traceSegment_069_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2362 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2349 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2349 13 14, g32p_row02_traceSegment_069_2349_0013, g32p_row02_traceSegment_069_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2322 54 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2322 27 27, g32p_row02_traceSegment_069_2322_0027, g32p_row02_traceSegment_069_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 2268 108 = [9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2268 54 54, g32p_row02_traceSegment_069_2268_0054, g32p_row02_traceSegment_069_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 2160 216 = [12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2160 108 108, g32p_row02_traceSegment_069_2160_0108, g32p_row02_traceSegment_069_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2376 13 14, g32p_row02_traceSegment_069_2376_0013, g32p_row02_traceSegment_069_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2403 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2403 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2403 13 14, g32p_row02_traceSegment_069_2403_0013, g32p_row02_traceSegment_069_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2376 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2376 27 27, g32p_row02_traceSegment_069_2376_0027, g32p_row02_traceSegment_069_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2430 13 14, g32p_row02_traceSegment_069_2430_0013, g32p_row02_traceSegment_069_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2457 13 14, g32p_row02_traceSegment_069_2457_0013, g32p_row02_traceSegment_069_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2430 27 27, g32p_row02_traceSegment_069_2430_0027, g32p_row02_traceSegment_069_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 2376 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2376 54 54, g32p_row02_traceSegment_069_2376_0054, g32p_row02_traceSegment_069_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2484 13 14, g32p_row02_traceSegment_069_2484_0013, g32p_row02_traceSegment_069_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2511 13 14, g32p_row02_traceSegment_069_2511_0013, g32p_row02_traceSegment_069_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2484 27 27, g32p_row02_traceSegment_069_2484_0027, g32p_row02_traceSegment_069_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2538 13 14, g32p_row02_traceSegment_069_2538_0013, g32p_row02_traceSegment_069_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2565 13 14, g32p_row02_traceSegment_069_2565_0013, g32p_row02_traceSegment_069_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2538 27 27, g32p_row02_traceSegment_069_2538_0027, g32p_row02_traceSegment_069_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2484 54 54, g32p_row02_traceSegment_069_2484_0054, g32p_row02_traceSegment_069_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 2376 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2376 108 108, g32p_row02_traceSegment_069_2376_0108, g32p_row02_traceSegment_069_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_069 2160 432 = [14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2160 216 216, g32p_row02_traceSegment_069_2160_0216, g32p_row02_traceSegment_069_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_069 1728 864 = [14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1728 432 432, g32p_row02_traceSegment_069_1728_0432, g32p_row02_traceSegment_069_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2592 13 14, g32p_row02_traceSegment_069_2592_0013, g32p_row02_traceSegment_069_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2619 13 14, g32p_row02_traceSegment_069_2619_0013, g32p_row02_traceSegment_069_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2592 27 27, g32p_row02_traceSegment_069_2592_0027, g32p_row02_traceSegment_069_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2646 13 14, g32p_row02_traceSegment_069_2646_0013, g32p_row02_traceSegment_069_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2673 13 14, g32p_row02_traceSegment_069_2673_0013, g32p_row02_traceSegment_069_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2646 27 27, g32p_row02_traceSegment_069_2646_0027, g32p_row02_traceSegment_069_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2592 54 54, g32p_row02_traceSegment_069_2592_0054, g32p_row02_traceSegment_069_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2700 13 14, g32p_row02_traceSegment_069_2700_0013, g32p_row02_traceSegment_069_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2727 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2727 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2727 13 14, g32p_row02_traceSegment_069_2727_0013, g32p_row02_traceSegment_069_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2700 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2700 27 27, g32p_row02_traceSegment_069_2700_0027, g32p_row02_traceSegment_069_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2754 13 14, g32p_row02_traceSegment_069_2754_0013, g32p_row02_traceSegment_069_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2781 13 14, g32p_row02_traceSegment_069_2781_0013, g32p_row02_traceSegment_069_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2754 27 27, g32p_row02_traceSegment_069_2754_0027, g32p_row02_traceSegment_069_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 2700 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2700 54 54, g32p_row02_traceSegment_069_2700_0054, g32p_row02_traceSegment_069_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 2592 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2592 108 108, g32p_row02_traceSegment_069_2592_0108, g32p_row02_traceSegment_069_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2808 13 14, g32p_row02_traceSegment_069_2808_0013, g32p_row02_traceSegment_069_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2835 13 14, g32p_row02_traceSegment_069_2835_0013, g32p_row02_traceSegment_069_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2808 27 27, g32p_row02_traceSegment_069_2808_0027, g32p_row02_traceSegment_069_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2862 13 14, g32p_row02_traceSegment_069_2862_0013, g32p_row02_traceSegment_069_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2889 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2889 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2889 13 14, g32p_row02_traceSegment_069_2889_0013, g32p_row02_traceSegment_069_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2862 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2862 27 27, g32p_row02_traceSegment_069_2862_0027, g32p_row02_traceSegment_069_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 2808 108 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2808 54 54, g32p_row02_traceSegment_069_2808_0054, g32p_row02_traceSegment_069_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2916 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2929 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2916 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2916 13 14, g32p_row02_traceSegment_069_2916_0013, g32p_row02_traceSegment_069_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2956 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2943 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2943 13 14, g32p_row02_traceSegment_069_2943_0013, g32p_row02_traceSegment_069_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2916 54 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2916 27 27, g32p_row02_traceSegment_069_2916_0027, g32p_row02_traceSegment_069_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 2983 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2970 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2970 13 14, g32p_row02_traceSegment_069_2970_0013, g32p_row02_traceSegment_069_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 2997 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 2997 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2997 13 14, g32p_row02_traceSegment_069_2997_0013, g32p_row02_traceSegment_069_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 2970 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2970 27 27, g32p_row02_traceSegment_069_2970_0027, g32p_row02_traceSegment_069_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 2916 108 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2916 54 54, g32p_row02_traceSegment_069_2916_0054, g32p_row02_traceSegment_069_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 2808 216 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2808 108 108, g32p_row02_traceSegment_069_2808_0108, g32p_row02_traceSegment_069_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_069 2592 432 = [1, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2592 216 216, g32p_row02_traceSegment_069_2592_0216, g32p_row02_traceSegment_069_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3024 13 14, g32p_row02_traceSegment_069_3024_0013, g32p_row02_traceSegment_069_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3051 13 14, g32p_row02_traceSegment_069_3051_0013, g32p_row02_traceSegment_069_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3024 27 27, g32p_row02_traceSegment_069_3024_0027, g32p_row02_traceSegment_069_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3078 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3091 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3078 27 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3078 13 14, g32p_row02_traceSegment_069_3078_0013, g32p_row02_traceSegment_069_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3105 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3105 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3105 13 14, g32p_row02_traceSegment_069_3105_0013, g32p_row02_traceSegment_069_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 3078 54 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3078 27 27, g32p_row02_traceSegment_069_3078_0027, g32p_row02_traceSegment_069_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 3024 108 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3024 54 54, g32p_row02_traceSegment_069_3024_0054, g32p_row02_traceSegment_069_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3132 13 14, g32p_row02_traceSegment_069_3132_0013, g32p_row02_traceSegment_069_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3159 13 14, g32p_row02_traceSegment_069_3159_0013, g32p_row02_traceSegment_069_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3132 27 27, g32p_row02_traceSegment_069_3132_0027, g32p_row02_traceSegment_069_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3186 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3199 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3186 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3186 13 14, g32p_row02_traceSegment_069_3186_0013, g32p_row02_traceSegment_069_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3226 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3213 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3213 13 14, g32p_row02_traceSegment_069_3213_0013, g32p_row02_traceSegment_069_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 3186 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3186 27 27, g32p_row02_traceSegment_069_3186_0027, g32p_row02_traceSegment_069_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 3132 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3132 54 54, g32p_row02_traceSegment_069_3132_0054, g32p_row02_traceSegment_069_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 3024 216 = [1, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3024 108 108, g32p_row02_traceSegment_069_3024_0108, g32p_row02_traceSegment_069_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3240 13 14, g32p_row02_traceSegment_069_3240_0013, g32p_row02_traceSegment_069_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3267 13 14, g32p_row02_traceSegment_069_3267_0013, g32p_row02_traceSegment_069_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3240 27 27, g32p_row02_traceSegment_069_3240_0027, g32p_row02_traceSegment_069_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3294 13 14, g32p_row02_traceSegment_069_3294_0013, g32p_row02_traceSegment_069_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3321 13 14, g32p_row02_traceSegment_069_3321_0013, g32p_row02_traceSegment_069_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3294 27 27, g32p_row02_traceSegment_069_3294_0027, g32p_row02_traceSegment_069_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3240 54 54, g32p_row02_traceSegment_069_3240_0054, g32p_row02_traceSegment_069_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3348 13 14, g32p_row02_traceSegment_069_3348_0013, g32p_row02_traceSegment_069_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3375 13 14, g32p_row02_traceSegment_069_3375_0013, g32p_row02_traceSegment_069_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3348 27 27, g32p_row02_traceSegment_069_3348_0027, g32p_row02_traceSegment_069_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3402 13 14, g32p_row02_traceSegment_069_3402_0013, g32p_row02_traceSegment_069_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_069 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_069 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_069_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_069 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3429 13 14, g32p_row02_traceSegment_069_3429_0013, g32p_row02_traceSegment_069_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_069 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3402 27 27, g32p_row02_traceSegment_069_3402_0027, g32p_row02_traceSegment_069_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_069 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3348 54 54, g32p_row02_traceSegment_069_3348_0054, g32p_row02_traceSegment_069_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_069 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3240 108 108, g32p_row02_traceSegment_069_3240_0108, g32p_row02_traceSegment_069_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_069_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_069 3024 432 = [1, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 3024 216 216, g32p_row02_traceSegment_069_3024_0216, g32p_row02_traceSegment_069_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_069_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_069 2592 864 = [2, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 2592 432 432, g32p_row02_traceSegment_069_2592_0432, g32p_row02_traceSegment_069_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_069_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_069 1728 1728 = [16, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 1728 864 864, g32p_row02_traceSegment_069_1728_0864, g32p_row02_traceSegment_069_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_069_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_069 0 3456 = [36, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_069 0 1728 1728, g32p_row02_traceSegment_069_0000_1728, g32p_row02_traceSegment_069_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 69 = [36, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_069_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_071 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 71 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_071_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 0 13 14, g32p_row02_traceSegment_071_0000_0013, g32p_row02_traceSegment_071_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 27 13 14, g32p_row02_traceSegment_071_0027_0013, g32p_row02_traceSegment_071_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 0 27 27, g32p_row02_traceSegment_071_0000_0027, g32p_row02_traceSegment_071_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 54 13 14, g32p_row02_traceSegment_071_0054_0013, g32p_row02_traceSegment_071_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 81 13 14, g32p_row02_traceSegment_071_0081_0013, g32p_row02_traceSegment_071_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 54 27 27, g32p_row02_traceSegment_071_0054_0027, g32p_row02_traceSegment_071_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 0 54 54, g32p_row02_traceSegment_071_0000_0054, g32p_row02_traceSegment_071_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 108 13 14, g32p_row02_traceSegment_071_0108_0013, g32p_row02_traceSegment_071_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 135 13 14, g32p_row02_traceSegment_071_0135_0013, g32p_row02_traceSegment_071_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 108 27 27, g32p_row02_traceSegment_071_0108_0027, g32p_row02_traceSegment_071_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 162 13 14, g32p_row02_traceSegment_071_0162_0013, g32p_row02_traceSegment_071_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 189 13 14, g32p_row02_traceSegment_071_0189_0013, g32p_row02_traceSegment_071_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 162 27 27, g32p_row02_traceSegment_071_0162_0027, g32p_row02_traceSegment_071_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 108 54 54, g32p_row02_traceSegment_071_0108_0054, g32p_row02_traceSegment_071_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 0 108 108, g32p_row02_traceSegment_071_0000_0108, g32p_row02_traceSegment_071_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 216 13 14, g32p_row02_traceSegment_071_0216_0013, g32p_row02_traceSegment_071_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 243 13 14, g32p_row02_traceSegment_071_0243_0013, g32p_row02_traceSegment_071_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 216 27 27, g32p_row02_traceSegment_071_0216_0027, g32p_row02_traceSegment_071_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 270 13 14, g32p_row02_traceSegment_071_0270_0013, g32p_row02_traceSegment_071_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 297 13 14, g32p_row02_traceSegment_071_0297_0013, g32p_row02_traceSegment_071_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 270 27 27, g32p_row02_traceSegment_071_0270_0027, g32p_row02_traceSegment_071_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 216 54 54, g32p_row02_traceSegment_071_0216_0054, g32p_row02_traceSegment_071_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 324 13 14, g32p_row02_traceSegment_071_0324_0013, g32p_row02_traceSegment_071_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 351 13 14, g32p_row02_traceSegment_071_0351_0013, g32p_row02_traceSegment_071_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 324 27 27, g32p_row02_traceSegment_071_0324_0027, g32p_row02_traceSegment_071_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 378 13 14, g32p_row02_traceSegment_071_0378_0013, g32p_row02_traceSegment_071_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 405 13 14, g32p_row02_traceSegment_071_0405_0013, g32p_row02_traceSegment_071_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 378 27 27, g32p_row02_traceSegment_071_0378_0027, g32p_row02_traceSegment_071_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 324 54 54, g32p_row02_traceSegment_071_0324_0054, g32p_row02_traceSegment_071_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 216 108 108, g32p_row02_traceSegment_071_0216_0108, g32p_row02_traceSegment_071_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_071 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 0 216 216, g32p_row02_traceSegment_071_0000_0216, g32p_row02_traceSegment_071_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 432 13 14, g32p_row02_traceSegment_071_0432_0013, g32p_row02_traceSegment_071_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 459 13 14, g32p_row02_traceSegment_071_0459_0013, g32p_row02_traceSegment_071_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 432 27 27, g32p_row02_traceSegment_071_0432_0027, g32p_row02_traceSegment_071_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 486 13 14, g32p_row02_traceSegment_071_0486_0013, g32p_row02_traceSegment_071_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 513 13 14, g32p_row02_traceSegment_071_0513_0013, g32p_row02_traceSegment_071_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 486 27 27, g32p_row02_traceSegment_071_0486_0027, g32p_row02_traceSegment_071_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 432 54 54, g32p_row02_traceSegment_071_0432_0054, g32p_row02_traceSegment_071_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 540 13 14, g32p_row02_traceSegment_071_0540_0013, g32p_row02_traceSegment_071_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 567 13 14, g32p_row02_traceSegment_071_0567_0013, g32p_row02_traceSegment_071_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 540 27 27, g32p_row02_traceSegment_071_0540_0027, g32p_row02_traceSegment_071_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 594 13 14, g32p_row02_traceSegment_071_0594_0013, g32p_row02_traceSegment_071_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 621 13 14, g32p_row02_traceSegment_071_0621_0013, g32p_row02_traceSegment_071_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 594 27 27, g32p_row02_traceSegment_071_0594_0027, g32p_row02_traceSegment_071_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 540 54 54, g32p_row02_traceSegment_071_0540_0054, g32p_row02_traceSegment_071_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 432 108 108, g32p_row02_traceSegment_071_0432_0108, g32p_row02_traceSegment_071_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 648 13 14, g32p_row02_traceSegment_071_0648_0013, g32p_row02_traceSegment_071_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 675 13 14, g32p_row02_traceSegment_071_0675_0013, g32p_row02_traceSegment_071_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 648 27 27, g32p_row02_traceSegment_071_0648_0027, g32p_row02_traceSegment_071_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 702 13 14, g32p_row02_traceSegment_071_0702_0013, g32p_row02_traceSegment_071_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 729 13 14, g32p_row02_traceSegment_071_0729_0013, g32p_row02_traceSegment_071_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 702 27 27, g32p_row02_traceSegment_071_0702_0027, g32p_row02_traceSegment_071_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 648 54 54, g32p_row02_traceSegment_071_0648_0054, g32p_row02_traceSegment_071_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 756 13 14, g32p_row02_traceSegment_071_0756_0013, g32p_row02_traceSegment_071_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 783 13 14, g32p_row02_traceSegment_071_0783_0013, g32p_row02_traceSegment_071_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 756 27 27, g32p_row02_traceSegment_071_0756_0027, g32p_row02_traceSegment_071_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 810 13 14, g32p_row02_traceSegment_071_0810_0013, g32p_row02_traceSegment_071_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 837 13 14, g32p_row02_traceSegment_071_0837_0013, g32p_row02_traceSegment_071_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 810 27 27, g32p_row02_traceSegment_071_0810_0027, g32p_row02_traceSegment_071_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 756 54 54, g32p_row02_traceSegment_071_0756_0054, g32p_row02_traceSegment_071_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 648 108 108, g32p_row02_traceSegment_071_0648_0108, g32p_row02_traceSegment_071_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_071 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 432 216 216, g32p_row02_traceSegment_071_0432_0216, g32p_row02_traceSegment_071_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_071 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 0 432 432, g32p_row02_traceSegment_071_0000_0432, g32p_row02_traceSegment_071_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 864 13 14, g32p_row02_traceSegment_071_0864_0013, g32p_row02_traceSegment_071_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 891 13 14, g32p_row02_traceSegment_071_0891_0013, g32p_row02_traceSegment_071_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 864 27 27, g32p_row02_traceSegment_071_0864_0027, g32p_row02_traceSegment_071_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 918 13 14, g32p_row02_traceSegment_071_0918_0013, g32p_row02_traceSegment_071_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 945 13 14, g32p_row02_traceSegment_071_0945_0013, g32p_row02_traceSegment_071_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 918 27 27, g32p_row02_traceSegment_071_0918_0027, g32p_row02_traceSegment_071_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 864 54 54, g32p_row02_traceSegment_071_0864_0054, g32p_row02_traceSegment_071_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 972 13 14, g32p_row02_traceSegment_071_0972_0013, g32p_row02_traceSegment_071_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 999 13 14, g32p_row02_traceSegment_071_0999_0013, g32p_row02_traceSegment_071_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 972 27 27, g32p_row02_traceSegment_071_0972_0027, g32p_row02_traceSegment_071_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1026 13 14, g32p_row02_traceSegment_071_1026_0013, g32p_row02_traceSegment_071_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1053 13 14, g32p_row02_traceSegment_071_1053_0013, g32p_row02_traceSegment_071_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1026 27 27, g32p_row02_traceSegment_071_1026_0027, g32p_row02_traceSegment_071_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 972 54 54, g32p_row02_traceSegment_071_0972_0054, g32p_row02_traceSegment_071_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 864 108 108, g32p_row02_traceSegment_071_0864_0108, g32p_row02_traceSegment_071_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1080 13 14, g32p_row02_traceSegment_071_1080_0013, g32p_row02_traceSegment_071_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1107 13 14, g32p_row02_traceSegment_071_1107_0013, g32p_row02_traceSegment_071_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1080 27 27, g32p_row02_traceSegment_071_1080_0027, g32p_row02_traceSegment_071_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1134 13 14, g32p_row02_traceSegment_071_1134_0013, g32p_row02_traceSegment_071_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1161 13 14, g32p_row02_traceSegment_071_1161_0013, g32p_row02_traceSegment_071_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1134 27 27, g32p_row02_traceSegment_071_1134_0027, g32p_row02_traceSegment_071_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1080 54 54, g32p_row02_traceSegment_071_1080_0054, g32p_row02_traceSegment_071_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1188 13 14, g32p_row02_traceSegment_071_1188_0013, g32p_row02_traceSegment_071_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1215 13 14, g32p_row02_traceSegment_071_1215_0013, g32p_row02_traceSegment_071_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1188 27 27, g32p_row02_traceSegment_071_1188_0027, g32p_row02_traceSegment_071_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1242 13 14, g32p_row02_traceSegment_071_1242_0013, g32p_row02_traceSegment_071_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1269 13 14, g32p_row02_traceSegment_071_1269_0013, g32p_row02_traceSegment_071_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1242 27 27, g32p_row02_traceSegment_071_1242_0027, g32p_row02_traceSegment_071_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1188 54 54, g32p_row02_traceSegment_071_1188_0054, g32p_row02_traceSegment_071_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1080 108 108, g32p_row02_traceSegment_071_1080_0108, g32p_row02_traceSegment_071_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_071 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 864 216 216, g32p_row02_traceSegment_071_0864_0216, g32p_row02_traceSegment_071_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1296 13 14, g32p_row02_traceSegment_071_1296_0013, g32p_row02_traceSegment_071_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1323 13 14, g32p_row02_traceSegment_071_1323_0013, g32p_row02_traceSegment_071_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1296 27 27, g32p_row02_traceSegment_071_1296_0027, g32p_row02_traceSegment_071_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1350 13 14, g32p_row02_traceSegment_071_1350_0013, g32p_row02_traceSegment_071_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1377 13 14, g32p_row02_traceSegment_071_1377_0013, g32p_row02_traceSegment_071_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1350 27 27, g32p_row02_traceSegment_071_1350_0027, g32p_row02_traceSegment_071_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1296 54 54, g32p_row02_traceSegment_071_1296_0054, g32p_row02_traceSegment_071_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1404 13 14, g32p_row02_traceSegment_071_1404_0013, g32p_row02_traceSegment_071_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1431 13 14, g32p_row02_traceSegment_071_1431_0013, g32p_row02_traceSegment_071_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1404 27 27, g32p_row02_traceSegment_071_1404_0027, g32p_row02_traceSegment_071_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1458 13 14, g32p_row02_traceSegment_071_1458_0013, g32p_row02_traceSegment_071_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1485 13 14, g32p_row02_traceSegment_071_1485_0013, g32p_row02_traceSegment_071_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1458 27 27, g32p_row02_traceSegment_071_1458_0027, g32p_row02_traceSegment_071_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1404 54 54, g32p_row02_traceSegment_071_1404_0054, g32p_row02_traceSegment_071_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1296 108 108, g32p_row02_traceSegment_071_1296_0108, g32p_row02_traceSegment_071_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1512 13 14, g32p_row02_traceSegment_071_1512_0013, g32p_row02_traceSegment_071_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1539 13 14, g32p_row02_traceSegment_071_1539_0013, g32p_row02_traceSegment_071_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1512 27 27, g32p_row02_traceSegment_071_1512_0027, g32p_row02_traceSegment_071_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1566 13 14, g32p_row02_traceSegment_071_1566_0013, g32p_row02_traceSegment_071_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1593 13 14, g32p_row02_traceSegment_071_1593_0013, g32p_row02_traceSegment_071_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1566 27 27, g32p_row02_traceSegment_071_1566_0027, g32p_row02_traceSegment_071_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1512 54 54, g32p_row02_traceSegment_071_1512_0054, g32p_row02_traceSegment_071_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1633 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1620 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1620 13 14, g32p_row02_traceSegment_071_1620_0013, g32p_row02_traceSegment_071_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1647 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1647 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1647 13 14, g32p_row02_traceSegment_071_1647_0013, g32p_row02_traceSegment_071_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1620 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1620 27 27, g32p_row02_traceSegment_071_1620_0027, g32p_row02_traceSegment_071_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1674 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1674 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1674 13 14, g32p_row02_traceSegment_071_1674_0013, g32p_row02_traceSegment_071_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1701 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1701 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1701 13 14, g32p_row02_traceSegment_071_1701_0013, g32p_row02_traceSegment_071_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1674 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1674 27 27, g32p_row02_traceSegment_071_1674_0027, g32p_row02_traceSegment_071_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 1620 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1620 54 54, g32p_row02_traceSegment_071_1620_0054, g32p_row02_traceSegment_071_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 1512 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1512 108 108, g32p_row02_traceSegment_071_1512_0108, g32p_row02_traceSegment_071_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_071 1296 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1296 216 216, g32p_row02_traceSegment_071_1296_0216, g32p_row02_traceSegment_071_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_071 864 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 864 432 432, g32p_row02_traceSegment_071_0864_0432, g32p_row02_traceSegment_071_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_071 0 1728 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 0 864 864, g32p_row02_traceSegment_071_0000_0864, g32p_row02_traceSegment_071_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1728 13 14, g32p_row02_traceSegment_071_1728_0013, g32p_row02_traceSegment_071_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1755 13 14, g32p_row02_traceSegment_071_1755_0013, g32p_row02_traceSegment_071_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1728 27 27, g32p_row02_traceSegment_071_1728_0027, g32p_row02_traceSegment_071_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1782 13 14, g32p_row02_traceSegment_071_1782_0013, g32p_row02_traceSegment_071_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1809 13 14, g32p_row02_traceSegment_071_1809_0013, g32p_row02_traceSegment_071_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1782 27 27, g32p_row02_traceSegment_071_1782_0027, g32p_row02_traceSegment_071_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1728 54 54, g32p_row02_traceSegment_071_1728_0054, g32p_row02_traceSegment_071_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1836 13 14, g32p_row02_traceSegment_071_1836_0013, g32p_row02_traceSegment_071_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1863 13 14, g32p_row02_traceSegment_071_1863_0013, g32p_row02_traceSegment_071_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1836 27 27, g32p_row02_traceSegment_071_1836_0027, g32p_row02_traceSegment_071_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1890 13 14, g32p_row02_traceSegment_071_1890_0013, g32p_row02_traceSegment_071_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1930 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1917 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1917 13 14, g32p_row02_traceSegment_071_1917_0013, g32p_row02_traceSegment_071_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1890 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1890 27 27, g32p_row02_traceSegment_071_1890_0027, g32p_row02_traceSegment_071_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 1836 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1836 54 54, g32p_row02_traceSegment_071_1836_0054, g32p_row02_traceSegment_071_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 1728 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1728 108 108, g32p_row02_traceSegment_071_1728_0108, g32p_row02_traceSegment_071_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1944 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1957 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1944 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1944 13 14, g32p_row02_traceSegment_071_1944_0013, g32p_row02_traceSegment_071_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1971 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 1984 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1971 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1971 13 14, g32p_row02_traceSegment_071_1971_0013, g32p_row02_traceSegment_071_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1944 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1944 27 27, g32p_row02_traceSegment_071_1944_0027, g32p_row02_traceSegment_071_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 1998 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2011 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 1998 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1998 13 14, g32p_row02_traceSegment_071_1998_0013, g32p_row02_traceSegment_071_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2038 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2025 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2025 13 14, g32p_row02_traceSegment_071_2025_0013, g32p_row02_traceSegment_071_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 1998 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1998 27 27, g32p_row02_traceSegment_071_1998_0027, g32p_row02_traceSegment_071_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 1944 108 = [7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1944 54 54, g32p_row02_traceSegment_071_1944_0054, g32p_row02_traceSegment_071_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2052 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2065 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2052 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2052 13 14, g32p_row02_traceSegment_071_2052_0013, g32p_row02_traceSegment_071_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2079 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2092 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2079 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2079 13 14, g32p_row02_traceSegment_071_2079_0013, g32p_row02_traceSegment_071_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2052 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2052 27 27, g32p_row02_traceSegment_071_2052_0027, g32p_row02_traceSegment_071_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2119 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2106 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2106 13 14, g32p_row02_traceSegment_071_2106_0013, g32p_row02_traceSegment_071_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2146 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2133 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2133 13 14, g32p_row02_traceSegment_071_2133_0013, g32p_row02_traceSegment_071_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2106 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2106 27 27, g32p_row02_traceSegment_071_2106_0027, g32p_row02_traceSegment_071_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 2052 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2052 54 54, g32p_row02_traceSegment_071_2052_0054, g32p_row02_traceSegment_071_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 1944 216 = [13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1944 108 108, g32p_row02_traceSegment_071_1944_0108, g32p_row02_traceSegment_071_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_071 1728 432 = [15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1728 216 216, g32p_row02_traceSegment_071_1728_0216, g32p_row02_traceSegment_071_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2160 13 14, g32p_row02_traceSegment_071_2160_0013, g32p_row02_traceSegment_071_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2187 13 14, g32p_row02_traceSegment_071_2187_0013, g32p_row02_traceSegment_071_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2160 27 27, g32p_row02_traceSegment_071_2160_0027, g32p_row02_traceSegment_071_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2214 13 14, g32p_row02_traceSegment_071_2214_0013, g32p_row02_traceSegment_071_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2241 13 14, g32p_row02_traceSegment_071_2241_0013, g32p_row02_traceSegment_071_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2214 27 27, g32p_row02_traceSegment_071_2214_0027, g32p_row02_traceSegment_071_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2160 54 54, g32p_row02_traceSegment_071_2160_0054, g32p_row02_traceSegment_071_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2268 13 14, g32p_row02_traceSegment_071_2268_0013, g32p_row02_traceSegment_071_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2295 13 14, g32p_row02_traceSegment_071_2295_0013, g32p_row02_traceSegment_071_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2268 27 27, g32p_row02_traceSegment_071_2268_0027, g32p_row02_traceSegment_071_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2322 13 14, g32p_row02_traceSegment_071_2322_0013, g32p_row02_traceSegment_071_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2349 13 14, g32p_row02_traceSegment_071_2349_0013, g32p_row02_traceSegment_071_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2322 27 27, g32p_row02_traceSegment_071_2322_0027, g32p_row02_traceSegment_071_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2268 54 54, g32p_row02_traceSegment_071_2268_0054, g32p_row02_traceSegment_071_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2160 108 108, g32p_row02_traceSegment_071_2160_0108, g32p_row02_traceSegment_071_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2376 13 14, g32p_row02_traceSegment_071_2376_0013, g32p_row02_traceSegment_071_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2403 13 14, g32p_row02_traceSegment_071_2403_0013, g32p_row02_traceSegment_071_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2376 27 27, g32p_row02_traceSegment_071_2376_0027, g32p_row02_traceSegment_071_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2430 13 14, g32p_row02_traceSegment_071_2430_0013, g32p_row02_traceSegment_071_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2457 13 14, g32p_row02_traceSegment_071_2457_0013, g32p_row02_traceSegment_071_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2430 27 27, g32p_row02_traceSegment_071_2430_0027, g32p_row02_traceSegment_071_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2376 54 54, g32p_row02_traceSegment_071_2376_0054, g32p_row02_traceSegment_071_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2484 13 14, g32p_row02_traceSegment_071_2484_0013, g32p_row02_traceSegment_071_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2524 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2511 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2511 13 14, g32p_row02_traceSegment_071_2511_0013, g32p_row02_traceSegment_071_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2484 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2484 27 27, g32p_row02_traceSegment_071_2484_0027, g32p_row02_traceSegment_071_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2538 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2551 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2538 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2538 13 14, g32p_row02_traceSegment_071_2538_0013, g32p_row02_traceSegment_071_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2565 13 14, g32p_row02_traceSegment_071_2565_0013, g32p_row02_traceSegment_071_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2538 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2538 27 27, g32p_row02_traceSegment_071_2538_0027, g32p_row02_traceSegment_071_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 2484 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2484 54 54, g32p_row02_traceSegment_071_2484_0054, g32p_row02_traceSegment_071_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 2376 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2376 108 108, g32p_row02_traceSegment_071_2376_0108, g32p_row02_traceSegment_071_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_071 2160 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2160 216 216, g32p_row02_traceSegment_071_2160_0216, g32p_row02_traceSegment_071_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_071 1728 864 = [18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1728 432 432, g32p_row02_traceSegment_071_1728_0432, g32p_row02_traceSegment_071_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2592 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2592 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2592 13 14, g32p_row02_traceSegment_071_2592_0013, g32p_row02_traceSegment_071_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2619 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2632 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2619 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2619 13 14, g32p_row02_traceSegment_071_2619_0013, g32p_row02_traceSegment_071_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2592 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2592 27 27, g32p_row02_traceSegment_071_2592_0027, g32p_row02_traceSegment_071_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2646 13 14, g32p_row02_traceSegment_071_2646_0013, g32p_row02_traceSegment_071_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2673 13 14, g32p_row02_traceSegment_071_2673_0013, g32p_row02_traceSegment_071_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2646 27 27, g32p_row02_traceSegment_071_2646_0027, g32p_row02_traceSegment_071_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 2592 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2592 54 54, g32p_row02_traceSegment_071_2592_0054, g32p_row02_traceSegment_071_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2700 13 14, g32p_row02_traceSegment_071_2700_0013, g32p_row02_traceSegment_071_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2727 13 14, g32p_row02_traceSegment_071_2727_0013, g32p_row02_traceSegment_071_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2700 27 27, g32p_row02_traceSegment_071_2700_0027, g32p_row02_traceSegment_071_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2754 13 14, g32p_row02_traceSegment_071_2754_0013, g32p_row02_traceSegment_071_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2781 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2781 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2781 13 14, g32p_row02_traceSegment_071_2781_0013, g32p_row02_traceSegment_071_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2754 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2754 27 27, g32p_row02_traceSegment_071_2754_0027, g32p_row02_traceSegment_071_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 2700 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2700 54 54, g32p_row02_traceSegment_071_2700_0054, g32p_row02_traceSegment_071_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 2592 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2592 108 108, g32p_row02_traceSegment_071_2592_0108, g32p_row02_traceSegment_071_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2808 13 14, g32p_row02_traceSegment_071_2808_0013, g32p_row02_traceSegment_071_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2835 13 14, g32p_row02_traceSegment_071_2835_0013, g32p_row02_traceSegment_071_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2808 27 27, g32p_row02_traceSegment_071_2808_0027, g32p_row02_traceSegment_071_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2862 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2862 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2862 13 14, g32p_row02_traceSegment_071_2862_0013, g32p_row02_traceSegment_071_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2889 13 14, g32p_row02_traceSegment_071_2889_0013, g32p_row02_traceSegment_071_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2862 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2862 27 27, g32p_row02_traceSegment_071_2862_0027, g32p_row02_traceSegment_071_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 2808 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2808 54 54, g32p_row02_traceSegment_071_2808_0054, g32p_row02_traceSegment_071_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2916 13 14, g32p_row02_traceSegment_071_2916_0013, g32p_row02_traceSegment_071_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2943 13 14, g32p_row02_traceSegment_071_2943_0013, g32p_row02_traceSegment_071_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2916 27 27, g32p_row02_traceSegment_071_2916_0027, g32p_row02_traceSegment_071_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2970 13 14, g32p_row02_traceSegment_071_2970_0013, g32p_row02_traceSegment_071_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2997 13 14, g32p_row02_traceSegment_071_2997_0013, g32p_row02_traceSegment_071_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2970 27 27, g32p_row02_traceSegment_071_2970_0027, g32p_row02_traceSegment_071_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2916 54 54, g32p_row02_traceSegment_071_2916_0054, g32p_row02_traceSegment_071_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 2808 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2808 108 108, g32p_row02_traceSegment_071_2808_0108, g32p_row02_traceSegment_071_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_071 2592 432 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2592 216 216, g32p_row02_traceSegment_071_2592_0216, g32p_row02_traceSegment_071_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3024 13 14, g32p_row02_traceSegment_071_3024_0013, g32p_row02_traceSegment_071_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3051 13 14, g32p_row02_traceSegment_071_3051_0013, g32p_row02_traceSegment_071_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3024 27 27, g32p_row02_traceSegment_071_3024_0027, g32p_row02_traceSegment_071_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3078 13 14, g32p_row02_traceSegment_071_3078_0013, g32p_row02_traceSegment_071_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3105 13 14, g32p_row02_traceSegment_071_3105_0013, g32p_row02_traceSegment_071_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3078 27 27, g32p_row02_traceSegment_071_3078_0027, g32p_row02_traceSegment_071_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3024 54 54, g32p_row02_traceSegment_071_3024_0054, g32p_row02_traceSegment_071_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3132 13 14, g32p_row02_traceSegment_071_3132_0013, g32p_row02_traceSegment_071_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3159 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3172 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3159 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3159 13 14, g32p_row02_traceSegment_071_3159_0013, g32p_row02_traceSegment_071_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 3132 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3132 27 27, g32p_row02_traceSegment_071_3132_0027, g32p_row02_traceSegment_071_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3186 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3186 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3186 13 14, g32p_row02_traceSegment_071_3186_0013, g32p_row02_traceSegment_071_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3213 13 14, g32p_row02_traceSegment_071_3213_0013, g32p_row02_traceSegment_071_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 3186 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3186 27 27, g32p_row02_traceSegment_071_3186_0027, g32p_row02_traceSegment_071_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 3132 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3132 54 54, g32p_row02_traceSegment_071_3132_0054, g32p_row02_traceSegment_071_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 3024 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3024 108 108, g32p_row02_traceSegment_071_3024_0108, g32p_row02_traceSegment_071_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3240 13 14, g32p_row02_traceSegment_071_3240_0013, g32p_row02_traceSegment_071_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3267 13 14, g32p_row02_traceSegment_071_3267_0013, g32p_row02_traceSegment_071_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3240 27 27, g32p_row02_traceSegment_071_3240_0027, g32p_row02_traceSegment_071_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3294 13 14, g32p_row02_traceSegment_071_3294_0013, g32p_row02_traceSegment_071_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3321 13 14, g32p_row02_traceSegment_071_3321_0013, g32p_row02_traceSegment_071_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3294 27 27, g32p_row02_traceSegment_071_3294_0027, g32p_row02_traceSegment_071_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3240 54 54, g32p_row02_traceSegment_071_3240_0054, g32p_row02_traceSegment_071_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3348 13 14, g32p_row02_traceSegment_071_3348_0013, g32p_row02_traceSegment_071_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3375 13 14, g32p_row02_traceSegment_071_3375_0013, g32p_row02_traceSegment_071_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3348 27 27, g32p_row02_traceSegment_071_3348_0027, g32p_row02_traceSegment_071_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3415 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3402 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3402 13 14, g32p_row02_traceSegment_071_3402_0013, g32p_row02_traceSegment_071_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_071 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_071 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_071_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_071 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3429 13 14, g32p_row02_traceSegment_071_3429_0013, g32p_row02_traceSegment_071_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_071 3402 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3402 27 27, g32p_row02_traceSegment_071_3402_0027, g32p_row02_traceSegment_071_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_071 3348 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3348 54 54, g32p_row02_traceSegment_071_3348_0054, g32p_row02_traceSegment_071_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_071 3240 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3240 108 108, g32p_row02_traceSegment_071_3240_0108, g32p_row02_traceSegment_071_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_071_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_071 3024 432 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 3024 216 216, g32p_row02_traceSegment_071_3024_0216, g32p_row02_traceSegment_071_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_071_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_071 2592 864 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 2592 432 432, g32p_row02_traceSegment_071_2592_0432, g32p_row02_traceSegment_071_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_071_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_071 1728 1728 = [28] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 1728 864 864, g32p_row02_traceSegment_071_1728_0864, g32p_row02_traceSegment_071_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_071_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_071 0 3456 = [32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_071 0 1728 1728, g32p_row02_traceSegment_071_0000_1728, g32p_row02_traceSegment_071_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 71 = [32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_071_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_072 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 72 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_072_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 0 13 14, g32p_row02_traceSegment_072_0000_0013, g32p_row02_traceSegment_072_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 27 13 14, g32p_row02_traceSegment_072_0027_0013, g32p_row02_traceSegment_072_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 0 27 27, g32p_row02_traceSegment_072_0000_0027, g32p_row02_traceSegment_072_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 54 13 14, g32p_row02_traceSegment_072_0054_0013, g32p_row02_traceSegment_072_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 81 13 14, g32p_row02_traceSegment_072_0081_0013, g32p_row02_traceSegment_072_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 54 27 27, g32p_row02_traceSegment_072_0054_0027, g32p_row02_traceSegment_072_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 0 54 54, g32p_row02_traceSegment_072_0000_0054, g32p_row02_traceSegment_072_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 108 13 14, g32p_row02_traceSegment_072_0108_0013, g32p_row02_traceSegment_072_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 135 13 14, g32p_row02_traceSegment_072_0135_0013, g32p_row02_traceSegment_072_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 108 27 27, g32p_row02_traceSegment_072_0108_0027, g32p_row02_traceSegment_072_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 162 13 14, g32p_row02_traceSegment_072_0162_0013, g32p_row02_traceSegment_072_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 189 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 202 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 189 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 189 13 14, g32p_row02_traceSegment_072_0189_0013, g32p_row02_traceSegment_072_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 162 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 162 27 27, g32p_row02_traceSegment_072_0162_0027, g32p_row02_traceSegment_072_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 108 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 108 54 54, g32p_row02_traceSegment_072_0108_0054, g32p_row02_traceSegment_072_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 0 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 0 108 108, g32p_row02_traceSegment_072_0000_0108, g32p_row02_traceSegment_072_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 216 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 216 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 216 13 14, g32p_row02_traceSegment_072_0216_0013, g32p_row02_traceSegment_072_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 243 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 256 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 243 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 243 13 14, g32p_row02_traceSegment_072_0243_0013, g32p_row02_traceSegment_072_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 216 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 216 27 27, g32p_row02_traceSegment_072_0216_0027, g32p_row02_traceSegment_072_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 270 13 14, g32p_row02_traceSegment_072_0270_0013, g32p_row02_traceSegment_072_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 297 13 14, g32p_row02_traceSegment_072_0297_0013, g32p_row02_traceSegment_072_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 270 27 27, g32p_row02_traceSegment_072_0270_0027, g32p_row02_traceSegment_072_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 216 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 216 54 54, g32p_row02_traceSegment_072_0216_0054, g32p_row02_traceSegment_072_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 324 13 14, g32p_row02_traceSegment_072_0324_0013, g32p_row02_traceSegment_072_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 351 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 351 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 351 13 14, g32p_row02_traceSegment_072_0351_0013, g32p_row02_traceSegment_072_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 324 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 324 27 27, g32p_row02_traceSegment_072_0324_0027, g32p_row02_traceSegment_072_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 391 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 378 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 378 13 14, g32p_row02_traceSegment_072_0378_0013, g32p_row02_traceSegment_072_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 418 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 405 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 405 13 14, g32p_row02_traceSegment_072_0405_0013, g32p_row02_traceSegment_072_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 378 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 378 27 27, g32p_row02_traceSegment_072_0378_0027, g32p_row02_traceSegment_072_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 324 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 324 54 54, g32p_row02_traceSegment_072_0324_0054, g32p_row02_traceSegment_072_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 216 216 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 216 108 108, g32p_row02_traceSegment_072_0216_0108, g32p_row02_traceSegment_072_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_072 0 432 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 0 216 216, g32p_row02_traceSegment_072_0000_0216, g32p_row02_traceSegment_072_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 432 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 432 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 432 13 14, g32p_row02_traceSegment_072_0432_0013, g32p_row02_traceSegment_072_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 459 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 472 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 459 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 459 13 14, g32p_row02_traceSegment_072_0459_0013, g32p_row02_traceSegment_072_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 432 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 432 27 27, g32p_row02_traceSegment_072_0432_0027, g32p_row02_traceSegment_072_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 486 13 14, g32p_row02_traceSegment_072_0486_0013, g32p_row02_traceSegment_072_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 513 13 14, g32p_row02_traceSegment_072_0513_0013, g32p_row02_traceSegment_072_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 486 27 27, g32p_row02_traceSegment_072_0486_0027, g32p_row02_traceSegment_072_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 432 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 432 54 54, g32p_row02_traceSegment_072_0432_0054, g32p_row02_traceSegment_072_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 540 13 14, g32p_row02_traceSegment_072_0540_0013, g32p_row02_traceSegment_072_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 567 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 580 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 567 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 567 13 14, g32p_row02_traceSegment_072_0567_0013, g32p_row02_traceSegment_072_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 540 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 540 27 27, g32p_row02_traceSegment_072_0540_0027, g32p_row02_traceSegment_072_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 594 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 594 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 594 13 14, g32p_row02_traceSegment_072_0594_0013, g32p_row02_traceSegment_072_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 621 13 14, g32p_row02_traceSegment_072_0621_0013, g32p_row02_traceSegment_072_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 594 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 594 27 27, g32p_row02_traceSegment_072_0594_0027, g32p_row02_traceSegment_072_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 540 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 540 54 54, g32p_row02_traceSegment_072_0540_0054, g32p_row02_traceSegment_072_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 432 216 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 432 108 108, g32p_row02_traceSegment_072_0432_0108, g32p_row02_traceSegment_072_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 648 13 14, g32p_row02_traceSegment_072_0648_0013, g32p_row02_traceSegment_072_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 675 13 14, g32p_row02_traceSegment_072_0675_0013, g32p_row02_traceSegment_072_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 648 27 27, g32p_row02_traceSegment_072_0648_0027, g32p_row02_traceSegment_072_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 702 13 14, g32p_row02_traceSegment_072_0702_0013, g32p_row02_traceSegment_072_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 729 13 14, g32p_row02_traceSegment_072_0729_0013, g32p_row02_traceSegment_072_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 702 27 27, g32p_row02_traceSegment_072_0702_0027, g32p_row02_traceSegment_072_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 648 54 54, g32p_row02_traceSegment_072_0648_0054, g32p_row02_traceSegment_072_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 756 13 14, g32p_row02_traceSegment_072_0756_0013, g32p_row02_traceSegment_072_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 783 13 14, g32p_row02_traceSegment_072_0783_0013, g32p_row02_traceSegment_072_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 756 27 27, g32p_row02_traceSegment_072_0756_0027, g32p_row02_traceSegment_072_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 810 13 14, g32p_row02_traceSegment_072_0810_0013, g32p_row02_traceSegment_072_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 850 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 837 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 837 13 14, g32p_row02_traceSegment_072_0837_0013, g32p_row02_traceSegment_072_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 810 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 810 27 27, g32p_row02_traceSegment_072_0810_0027, g32p_row02_traceSegment_072_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 756 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 756 54 54, g32p_row02_traceSegment_072_0756_0054, g32p_row02_traceSegment_072_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 648 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 648 108 108, g32p_row02_traceSegment_072_0648_0108, g32p_row02_traceSegment_072_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_072 432 432 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 432 216 216, g32p_row02_traceSegment_072_0432_0216, g32p_row02_traceSegment_072_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_072 0 864 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 0 432 432, g32p_row02_traceSegment_072_0000_0432, g32p_row02_traceSegment_072_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 864 13 14, g32p_row02_traceSegment_072_0864_0013, g32p_row02_traceSegment_072_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 891 13 14, g32p_row02_traceSegment_072_0891_0013, g32p_row02_traceSegment_072_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 864 27 27, g32p_row02_traceSegment_072_0864_0027, g32p_row02_traceSegment_072_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 931 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 918 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 918 13 14, g32p_row02_traceSegment_072_0918_0013, g32p_row02_traceSegment_072_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 945 13 14, g32p_row02_traceSegment_072_0945_0013, g32p_row02_traceSegment_072_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 918 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 918 27 27, g32p_row02_traceSegment_072_0918_0027, g32p_row02_traceSegment_072_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 864 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 864 54 54, g32p_row02_traceSegment_072_0864_0054, g32p_row02_traceSegment_072_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 972 13 14, g32p_row02_traceSegment_072_0972_0013, g32p_row02_traceSegment_072_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 999 13 14, g32p_row02_traceSegment_072_0999_0013, g32p_row02_traceSegment_072_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 972 27 27, g32p_row02_traceSegment_072_0972_0027, g32p_row02_traceSegment_072_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1026 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1039 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1026 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1026 13 14, g32p_row02_traceSegment_072_1026_0013, g32p_row02_traceSegment_072_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1053 13 14, g32p_row02_traceSegment_072_1053_0013, g32p_row02_traceSegment_072_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1026 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1026 27 27, g32p_row02_traceSegment_072_1026_0027, g32p_row02_traceSegment_072_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 972 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 972 54 54, g32p_row02_traceSegment_072_0972_0054, g32p_row02_traceSegment_072_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 864 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 864 108 108, g32p_row02_traceSegment_072_0864_0108, g32p_row02_traceSegment_072_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1080 13 14, g32p_row02_traceSegment_072_1080_0013, g32p_row02_traceSegment_072_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1120 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1107 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1107 13 14, g32p_row02_traceSegment_072_1107_0013, g32p_row02_traceSegment_072_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1080 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1080 27 27, g32p_row02_traceSegment_072_1080_0027, g32p_row02_traceSegment_072_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1134 13 14, g32p_row02_traceSegment_072_1134_0013, g32p_row02_traceSegment_072_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1161 13 14, g32p_row02_traceSegment_072_1161_0013, g32p_row02_traceSegment_072_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1134 27 27, g32p_row02_traceSegment_072_1134_0027, g32p_row02_traceSegment_072_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 1080 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1080 54 54, g32p_row02_traceSegment_072_1080_0054, g32p_row02_traceSegment_072_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1188 13 14, g32p_row02_traceSegment_072_1188_0013, g32p_row02_traceSegment_072_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1215 13 14, g32p_row02_traceSegment_072_1215_0013, g32p_row02_traceSegment_072_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1188 27 27, g32p_row02_traceSegment_072_1188_0027, g32p_row02_traceSegment_072_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1242 13 14, g32p_row02_traceSegment_072_1242_0013, g32p_row02_traceSegment_072_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1269 13 14, g32p_row02_traceSegment_072_1269_0013, g32p_row02_traceSegment_072_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1242 27 27, g32p_row02_traceSegment_072_1242_0027, g32p_row02_traceSegment_072_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1188 54 54, g32p_row02_traceSegment_072_1188_0054, g32p_row02_traceSegment_072_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 1080 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1080 108 108, g32p_row02_traceSegment_072_1080_0108, g32p_row02_traceSegment_072_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_072 864 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 864 216 216, g32p_row02_traceSegment_072_0864_0216, g32p_row02_traceSegment_072_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1309 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1296 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1296 13 14, g32p_row02_traceSegment_072_1296_0013, g32p_row02_traceSegment_072_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1323 13 14, g32p_row02_traceSegment_072_1323_0013, g32p_row02_traceSegment_072_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1296 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1296 27 27, g32p_row02_traceSegment_072_1296_0027, g32p_row02_traceSegment_072_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1350 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1350 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1350 13 14, g32p_row02_traceSegment_072_1350_0013, g32p_row02_traceSegment_072_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1377 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1377 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1377 13 14, g32p_row02_traceSegment_072_1377_0013, g32p_row02_traceSegment_072_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1350 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1350 27 27, g32p_row02_traceSegment_072_1350_0027, g32p_row02_traceSegment_072_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 1296 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1296 54 54, g32p_row02_traceSegment_072_1296_0054, g32p_row02_traceSegment_072_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1404 13 14, g32p_row02_traceSegment_072_1404_0013, g32p_row02_traceSegment_072_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1431 13 14, g32p_row02_traceSegment_072_1431_0013, g32p_row02_traceSegment_072_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1404 27 27, g32p_row02_traceSegment_072_1404_0027, g32p_row02_traceSegment_072_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1471 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1458 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1458 13 14, g32p_row02_traceSegment_072_1458_0013, g32p_row02_traceSegment_072_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1485 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1485 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1485 13 14, g32p_row02_traceSegment_072_1485_0013, g32p_row02_traceSegment_072_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1458 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1458 27 27, g32p_row02_traceSegment_072_1458_0027, g32p_row02_traceSegment_072_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 1404 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1404 54 54, g32p_row02_traceSegment_072_1404_0054, g32p_row02_traceSegment_072_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 1296 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1296 108 108, g32p_row02_traceSegment_072_1296_0108, g32p_row02_traceSegment_072_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1512 13 14, g32p_row02_traceSegment_072_1512_0013, g32p_row02_traceSegment_072_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1539 13 14, g32p_row02_traceSegment_072_1539_0013, g32p_row02_traceSegment_072_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1512 27 27, g32p_row02_traceSegment_072_1512_0027, g32p_row02_traceSegment_072_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1566 13 14, g32p_row02_traceSegment_072_1566_0013, g32p_row02_traceSegment_072_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1606 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1593 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1593 13 14, g32p_row02_traceSegment_072_1593_0013, g32p_row02_traceSegment_072_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1566 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1566 27 27, g32p_row02_traceSegment_072_1566_0027, g32p_row02_traceSegment_072_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 1512 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1512 54 54, g32p_row02_traceSegment_072_1512_0054, g32p_row02_traceSegment_072_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1620 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1620 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1620 13 14, g32p_row02_traceSegment_072_1620_0013, g32p_row02_traceSegment_072_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1647 13 14, g32p_row02_traceSegment_072_1647_0013, g32p_row02_traceSegment_072_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1620 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1620 27 27, g32p_row02_traceSegment_072_1620_0027, g32p_row02_traceSegment_072_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1674 13 14, g32p_row02_traceSegment_072_1674_0013, g32p_row02_traceSegment_072_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1701 13 14, g32p_row02_traceSegment_072_1701_0013, g32p_row02_traceSegment_072_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1674 27 27, g32p_row02_traceSegment_072_1674_0027, g32p_row02_traceSegment_072_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 1620 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1620 54 54, g32p_row02_traceSegment_072_1620_0054, g32p_row02_traceSegment_072_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 1512 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1512 108 108, g32p_row02_traceSegment_072_1512_0108, g32p_row02_traceSegment_072_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_072 1296 432 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1296 216 216, g32p_row02_traceSegment_072_1296_0216, g32p_row02_traceSegment_072_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_072 864 864 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 864 432 432, g32p_row02_traceSegment_072_0864_0432, g32p_row02_traceSegment_072_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_072 0 1728 = [0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 0 864 864, g32p_row02_traceSegment_072_0000_0864, g32p_row02_traceSegment_072_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1728 13 14, g32p_row02_traceSegment_072_1728_0013, g32p_row02_traceSegment_072_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1755 13 14, g32p_row02_traceSegment_072_1755_0013, g32p_row02_traceSegment_072_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1728 27 27, g32p_row02_traceSegment_072_1728_0027, g32p_row02_traceSegment_072_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1795 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1782 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1782 13 14, g32p_row02_traceSegment_072_1782_0013, g32p_row02_traceSegment_072_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1809 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1809 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1809 13 14, g32p_row02_traceSegment_072_1809_0013, g32p_row02_traceSegment_072_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1782 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1782 27 27, g32p_row02_traceSegment_072_1782_0027, g32p_row02_traceSegment_072_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 1728 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1728 54 54, g32p_row02_traceSegment_072_1728_0054, g32p_row02_traceSegment_072_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1836 13 14, g32p_row02_traceSegment_072_1836_0013, g32p_row02_traceSegment_072_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1863 13 14, g32p_row02_traceSegment_072_1863_0013, g32p_row02_traceSegment_072_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1836 27 27, g32p_row02_traceSegment_072_1836_0027, g32p_row02_traceSegment_072_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1890 13 14, g32p_row02_traceSegment_072_1890_0013, g32p_row02_traceSegment_072_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1917 13 14, g32p_row02_traceSegment_072_1917_0013, g32p_row02_traceSegment_072_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1890 27 27, g32p_row02_traceSegment_072_1890_0027, g32p_row02_traceSegment_072_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1836 54 54, g32p_row02_traceSegment_072_1836_0054, g32p_row02_traceSegment_072_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 1728 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1728 108 108, g32p_row02_traceSegment_072_1728_0108, g32p_row02_traceSegment_072_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1944 13 14, g32p_row02_traceSegment_072_1944_0013, g32p_row02_traceSegment_072_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1971 13 14, g32p_row02_traceSegment_072_1971_0013, g32p_row02_traceSegment_072_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1944 27 27, g32p_row02_traceSegment_072_1944_0027, g32p_row02_traceSegment_072_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1998 13 14, g32p_row02_traceSegment_072_1998_0013, g32p_row02_traceSegment_072_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2025 13 14, g32p_row02_traceSegment_072_2025_0013, g32p_row02_traceSegment_072_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1998 27 27, g32p_row02_traceSegment_072_1998_0027, g32p_row02_traceSegment_072_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1944 54 54, g32p_row02_traceSegment_072_1944_0054, g32p_row02_traceSegment_072_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2052 13 14, g32p_row02_traceSegment_072_2052_0013, g32p_row02_traceSegment_072_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2079 13 14, g32p_row02_traceSegment_072_2079_0013, g32p_row02_traceSegment_072_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2052 27 27, g32p_row02_traceSegment_072_2052_0027, g32p_row02_traceSegment_072_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2106 13 14, g32p_row02_traceSegment_072_2106_0013, g32p_row02_traceSegment_072_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2133 13 14, g32p_row02_traceSegment_072_2133_0013, g32p_row02_traceSegment_072_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2106 27 27, g32p_row02_traceSegment_072_2106_0027, g32p_row02_traceSegment_072_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2052 54 54, g32p_row02_traceSegment_072_2052_0054, g32p_row02_traceSegment_072_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1944 108 108, g32p_row02_traceSegment_072_1944_0108, g32p_row02_traceSegment_072_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_072 1728 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1728 216 216, g32p_row02_traceSegment_072_1728_0216, g32p_row02_traceSegment_072_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2160 13 14, g32p_row02_traceSegment_072_2160_0013, g32p_row02_traceSegment_072_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2187 13 14, g32p_row02_traceSegment_072_2187_0013, g32p_row02_traceSegment_072_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2160 27 27, g32p_row02_traceSegment_072_2160_0027, g32p_row02_traceSegment_072_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2214 13 14, g32p_row02_traceSegment_072_2214_0013, g32p_row02_traceSegment_072_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2241 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2241 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2241 13 14, g32p_row02_traceSegment_072_2241_0013, g32p_row02_traceSegment_072_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2214 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2214 27 27, g32p_row02_traceSegment_072_2214_0027, g32p_row02_traceSegment_072_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 2160 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2160 54 54, g32p_row02_traceSegment_072_2160_0054, g32p_row02_traceSegment_072_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2268 13 14, g32p_row02_traceSegment_072_2268_0013, g32p_row02_traceSegment_072_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2295 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2295 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2295 13 14, g32p_row02_traceSegment_072_2295_0013, g32p_row02_traceSegment_072_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2268 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2268 27 27, g32p_row02_traceSegment_072_2268_0027, g32p_row02_traceSegment_072_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2322 13 14, g32p_row02_traceSegment_072_2322_0013, g32p_row02_traceSegment_072_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2349 13 14, g32p_row02_traceSegment_072_2349_0013, g32p_row02_traceSegment_072_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2322 27 27, g32p_row02_traceSegment_072_2322_0027, g32p_row02_traceSegment_072_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 2268 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2268 54 54, g32p_row02_traceSegment_072_2268_0054, g32p_row02_traceSegment_072_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 2160 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2160 108 108, g32p_row02_traceSegment_072_2160_0108, g32p_row02_traceSegment_072_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2376 13 14, g32p_row02_traceSegment_072_2376_0013, g32p_row02_traceSegment_072_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2403 13 14, g32p_row02_traceSegment_072_2403_0013, g32p_row02_traceSegment_072_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2376 27 27, g32p_row02_traceSegment_072_2376_0027, g32p_row02_traceSegment_072_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2430 13 14, g32p_row02_traceSegment_072_2430_0013, g32p_row02_traceSegment_072_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2457 13 14, g32p_row02_traceSegment_072_2457_0013, g32p_row02_traceSegment_072_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2430 27 27, g32p_row02_traceSegment_072_2430_0027, g32p_row02_traceSegment_072_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2376 54 54, g32p_row02_traceSegment_072_2376_0054, g32p_row02_traceSegment_072_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2484 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2484 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2484 13 14, g32p_row02_traceSegment_072_2484_0013, g32p_row02_traceSegment_072_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2511 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2524 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2511 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2511 13 14, g32p_row02_traceSegment_072_2511_0013, g32p_row02_traceSegment_072_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2484 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2484 27 27, g32p_row02_traceSegment_072_2484_0027, g32p_row02_traceSegment_072_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2538 13 14, g32p_row02_traceSegment_072_2538_0013, g32p_row02_traceSegment_072_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2565 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2565 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2565 13 14, g32p_row02_traceSegment_072_2565_0013, g32p_row02_traceSegment_072_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2538 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2538 27 27, g32p_row02_traceSegment_072_2538_0027, g32p_row02_traceSegment_072_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 2484 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2484 54 54, g32p_row02_traceSegment_072_2484_0054, g32p_row02_traceSegment_072_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 2376 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2376 108 108, g32p_row02_traceSegment_072_2376_0108, g32p_row02_traceSegment_072_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_072 2160 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2160 216 216, g32p_row02_traceSegment_072_2160_0216, g32p_row02_traceSegment_072_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_072 1728 864 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1728 432 432, g32p_row02_traceSegment_072_1728_0432, g32p_row02_traceSegment_072_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2592 13 14, g32p_row02_traceSegment_072_2592_0013, g32p_row02_traceSegment_072_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2619 13 14, g32p_row02_traceSegment_072_2619_0013, g32p_row02_traceSegment_072_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2592 27 27, g32p_row02_traceSegment_072_2592_0027, g32p_row02_traceSegment_072_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2646 13 14, g32p_row02_traceSegment_072_2646_0013, g32p_row02_traceSegment_072_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2673 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2673 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2673 13 14, g32p_row02_traceSegment_072_2673_0013, g32p_row02_traceSegment_072_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2646 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2646 27 27, g32p_row02_traceSegment_072_2646_0027, g32p_row02_traceSegment_072_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 2592 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2592 54 54, g32p_row02_traceSegment_072_2592_0054, g32p_row02_traceSegment_072_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2700 13 14, g32p_row02_traceSegment_072_2700_0013, g32p_row02_traceSegment_072_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2727 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2727 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2727 13 14, g32p_row02_traceSegment_072_2727_0013, g32p_row02_traceSegment_072_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2700 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2700 27 27, g32p_row02_traceSegment_072_2700_0027, g32p_row02_traceSegment_072_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2754 13 14, g32p_row02_traceSegment_072_2754_0013, g32p_row02_traceSegment_072_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2794 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2781 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2781 13 14, g32p_row02_traceSegment_072_2781_0013, g32p_row02_traceSegment_072_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2754 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2754 27 27, g32p_row02_traceSegment_072_2754_0027, g32p_row02_traceSegment_072_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 2700 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2700 54 54, g32p_row02_traceSegment_072_2700_0054, g32p_row02_traceSegment_072_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 2592 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2592 108 108, g32p_row02_traceSegment_072_2592_0108, g32p_row02_traceSegment_072_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2808 13 14, g32p_row02_traceSegment_072_2808_0013, g32p_row02_traceSegment_072_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2835 13 14, g32p_row02_traceSegment_072_2835_0013, g32p_row02_traceSegment_072_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2808 27 27, g32p_row02_traceSegment_072_2808_0027, g32p_row02_traceSegment_072_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2862 13 14, g32p_row02_traceSegment_072_2862_0013, g32p_row02_traceSegment_072_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2889 13 14, g32p_row02_traceSegment_072_2889_0013, g32p_row02_traceSegment_072_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2862 27 27, g32p_row02_traceSegment_072_2862_0027, g32p_row02_traceSegment_072_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2808 54 54, g32p_row02_traceSegment_072_2808_0054, g32p_row02_traceSegment_072_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2916 13 14, g32p_row02_traceSegment_072_2916_0013, g32p_row02_traceSegment_072_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2943 13 14, g32p_row02_traceSegment_072_2943_0013, g32p_row02_traceSegment_072_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2916 27 27, g32p_row02_traceSegment_072_2916_0027, g32p_row02_traceSegment_072_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2970 13 14, g32p_row02_traceSegment_072_2970_0013, g32p_row02_traceSegment_072_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3010 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 2997 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2997 13 14, g32p_row02_traceSegment_072_2997_0013, g32p_row02_traceSegment_072_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 2970 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2970 27 27, g32p_row02_traceSegment_072_2970_0027, g32p_row02_traceSegment_072_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 2916 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2916 54 54, g32p_row02_traceSegment_072_2916_0054, g32p_row02_traceSegment_072_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 2808 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2808 108 108, g32p_row02_traceSegment_072_2808_0108, g32p_row02_traceSegment_072_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_072 2592 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2592 216 216, g32p_row02_traceSegment_072_2592_0216, g32p_row02_traceSegment_072_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3024 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3037 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3024 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3024 13 14, g32p_row02_traceSegment_072_3024_0013, g32p_row02_traceSegment_072_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3051 13 14, g32p_row02_traceSegment_072_3051_0013, g32p_row02_traceSegment_072_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 3024 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3024 27 27, g32p_row02_traceSegment_072_3024_0027, g32p_row02_traceSegment_072_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3078 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3078 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3078 13 14, g32p_row02_traceSegment_072_3078_0013, g32p_row02_traceSegment_072_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3105 13 14, g32p_row02_traceSegment_072_3105_0013, g32p_row02_traceSegment_072_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 3078 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3078 27 27, g32p_row02_traceSegment_072_3078_0027, g32p_row02_traceSegment_072_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 3024 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3024 54 54, g32p_row02_traceSegment_072_3024_0054, g32p_row02_traceSegment_072_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3132 13 14, g32p_row02_traceSegment_072_3132_0013, g32p_row02_traceSegment_072_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3159 13 14, g32p_row02_traceSegment_072_3159_0013, g32p_row02_traceSegment_072_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3132 27 27, g32p_row02_traceSegment_072_3132_0027, g32p_row02_traceSegment_072_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3186 13 14, g32p_row02_traceSegment_072_3186_0013, g32p_row02_traceSegment_072_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3213 13 14, g32p_row02_traceSegment_072_3213_0013, g32p_row02_traceSegment_072_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3186 27 27, g32p_row02_traceSegment_072_3186_0027, g32p_row02_traceSegment_072_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3132 54 54, g32p_row02_traceSegment_072_3132_0054, g32p_row02_traceSegment_072_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 3024 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3024 108 108, g32p_row02_traceSegment_072_3024_0108, g32p_row02_traceSegment_072_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3253 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3240 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3240 13 14, g32p_row02_traceSegment_072_3240_0013, g32p_row02_traceSegment_072_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3280 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3267 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3267 13 14, g32p_row02_traceSegment_072_3267_0013, g32p_row02_traceSegment_072_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 3240 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3240 27 27, g32p_row02_traceSegment_072_3240_0027, g32p_row02_traceSegment_072_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3294 13 14, g32p_row02_traceSegment_072_3294_0013, g32p_row02_traceSegment_072_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3321 13 14, g32p_row02_traceSegment_072_3321_0013, g32p_row02_traceSegment_072_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3294 27 27, g32p_row02_traceSegment_072_3294_0027, g32p_row02_traceSegment_072_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 3240 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3240 54 54, g32p_row02_traceSegment_072_3240_0054, g32p_row02_traceSegment_072_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3348 13 14, g32p_row02_traceSegment_072_3348_0013, g32p_row02_traceSegment_072_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3375 13 14, g32p_row02_traceSegment_072_3375_0013, g32p_row02_traceSegment_072_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3348 27 27, g32p_row02_traceSegment_072_3348_0027, g32p_row02_traceSegment_072_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3402 13 14, g32p_row02_traceSegment_072_3402_0013, g32p_row02_traceSegment_072_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_072 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_072 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_072_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_072 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3429 13 14, g32p_row02_traceSegment_072_3429_0013, g32p_row02_traceSegment_072_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_072 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3402 27 27, g32p_row02_traceSegment_072_3402_0027, g32p_row02_traceSegment_072_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_072 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3348 54 54, g32p_row02_traceSegment_072_3348_0054, g32p_row02_traceSegment_072_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_072 3240 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3240 108 108, g32p_row02_traceSegment_072_3240_0108, g32p_row02_traceSegment_072_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_072_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_072 3024 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 3024 216 216, g32p_row02_traceSegment_072_3024_0216, g32p_row02_traceSegment_072_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_072_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_072 2592 864 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 2592 432 432, g32p_row02_traceSegment_072_2592_0432, g32p_row02_traceSegment_072_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_072_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_072 1728 1728 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 1728 864 864, g32p_row02_traceSegment_072_1728_0864, g32p_row02_traceSegment_072_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_072_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_072 0 3456 = [0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_072 0 1728 1728, g32p_row02_traceSegment_072_0000_1728, g32p_row02_traceSegment_072_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_072 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 72 = [0, 0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_072_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_063 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 63) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 63) (g32p_literalTraceValue 1 63)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_063]
  decide +kernel

theorem g32p_row02_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 64) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 64) (g32p_literalTraceValue 1 64)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_064]
  decide +kernel

theorem g32p_row02_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 65) (g32p_literalTraceValue 1 65)
      [1, -1, 1] [-38016, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_065]
  decide +kernel

theorem g32p_row02_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 66) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 66) (g32p_literalTraceValue 1 66)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_066]
  decide +kernel

theorem g32p_row02_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 67) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 67) (g32p_literalTraceValue 1 67)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_067]
  decide +kernel

theorem g32p_row02_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 69) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 69) (g32p_literalTraceValue 1 69)
      [1, -1, 1] [6912, 6912] = true := by
  rw [g32p_row02_traceCoefficients_069]
  decide +kernel

theorem g32p_row02_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 71) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 71) (g32p_literalTraceValue 1 71)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_071]
  decide +kernel

theorem g32p_row02_tracePolynomial_072 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 72) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 72) (g32p_literalTraceValue 1 72)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_072]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
