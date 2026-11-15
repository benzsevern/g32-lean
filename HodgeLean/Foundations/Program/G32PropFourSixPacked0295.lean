import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0294

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_015 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 15 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_015_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 0 13 14, g32p_row02_traceSegment_015_0000_0013, g32p_row02_traceSegment_015_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 27 13 14, g32p_row02_traceSegment_015_0027_0013, g32p_row02_traceSegment_015_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 0 27 27, g32p_row02_traceSegment_015_0000_0027, g32p_row02_traceSegment_015_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 54 13 14, g32p_row02_traceSegment_015_0054_0013, g32p_row02_traceSegment_015_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 81 13 14, g32p_row02_traceSegment_015_0081_0013, g32p_row02_traceSegment_015_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 54 27 27, g32p_row02_traceSegment_015_0054_0027, g32p_row02_traceSegment_015_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 0 54 54, g32p_row02_traceSegment_015_0000_0054, g32p_row02_traceSegment_015_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 108 13 14, g32p_row02_traceSegment_015_0108_0013, g32p_row02_traceSegment_015_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 135 13 14, g32p_row02_traceSegment_015_0135_0013, g32p_row02_traceSegment_015_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 108 27 27, g32p_row02_traceSegment_015_0108_0027, g32p_row02_traceSegment_015_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 162 13 14, g32p_row02_traceSegment_015_0162_0013, g32p_row02_traceSegment_015_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 189 13 14, g32p_row02_traceSegment_015_0189_0013, g32p_row02_traceSegment_015_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 162 27 27, g32p_row02_traceSegment_015_0162_0027, g32p_row02_traceSegment_015_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 108 54 54, g32p_row02_traceSegment_015_0108_0054, g32p_row02_traceSegment_015_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 0 108 108, g32p_row02_traceSegment_015_0000_0108, g32p_row02_traceSegment_015_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 216 13 14, g32p_row02_traceSegment_015_0216_0013, g32p_row02_traceSegment_015_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 243 13 14, g32p_row02_traceSegment_015_0243_0013, g32p_row02_traceSegment_015_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 216 27 27, g32p_row02_traceSegment_015_0216_0027, g32p_row02_traceSegment_015_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 270 13 14, g32p_row02_traceSegment_015_0270_0013, g32p_row02_traceSegment_015_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 297 13 14, g32p_row02_traceSegment_015_0297_0013, g32p_row02_traceSegment_015_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 270 27 27, g32p_row02_traceSegment_015_0270_0027, g32p_row02_traceSegment_015_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 216 54 54, g32p_row02_traceSegment_015_0216_0054, g32p_row02_traceSegment_015_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 324 13 14, g32p_row02_traceSegment_015_0324_0013, g32p_row02_traceSegment_015_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 351 13 14, g32p_row02_traceSegment_015_0351_0013, g32p_row02_traceSegment_015_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 324 27 27, g32p_row02_traceSegment_015_0324_0027, g32p_row02_traceSegment_015_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 378 13 14, g32p_row02_traceSegment_015_0378_0013, g32p_row02_traceSegment_015_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 405 13 14, g32p_row02_traceSegment_015_0405_0013, g32p_row02_traceSegment_015_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 378 27 27, g32p_row02_traceSegment_015_0378_0027, g32p_row02_traceSegment_015_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 324 54 54, g32p_row02_traceSegment_015_0324_0054, g32p_row02_traceSegment_015_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 216 108 108, g32p_row02_traceSegment_015_0216_0108, g32p_row02_traceSegment_015_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_015 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 0 216 216, g32p_row02_traceSegment_015_0000_0216, g32p_row02_traceSegment_015_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 432 13 14, g32p_row02_traceSegment_015_0432_0013, g32p_row02_traceSegment_015_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 459 13 14, g32p_row02_traceSegment_015_0459_0013, g32p_row02_traceSegment_015_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 432 27 27, g32p_row02_traceSegment_015_0432_0027, g32p_row02_traceSegment_015_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 486 13 14, g32p_row02_traceSegment_015_0486_0013, g32p_row02_traceSegment_015_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 526 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 513 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 513 13 14, g32p_row02_traceSegment_015_0513_0013, g32p_row02_traceSegment_015_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 486 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 486 27 27, g32p_row02_traceSegment_015_0486_0027, g32p_row02_traceSegment_015_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 432 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 432 54 54, g32p_row02_traceSegment_015_0432_0054, g32p_row02_traceSegment_015_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 553 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 540 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 540 13 14, g32p_row02_traceSegment_015_0540_0013, g32p_row02_traceSegment_015_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 567 13 14, g32p_row02_traceSegment_015_0567_0013, g32p_row02_traceSegment_015_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 540 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 540 27 27, g32p_row02_traceSegment_015_0540_0027, g32p_row02_traceSegment_015_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 594 13 14, g32p_row02_traceSegment_015_0594_0013, g32p_row02_traceSegment_015_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 621 13 14, g32p_row02_traceSegment_015_0621_0013, g32p_row02_traceSegment_015_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 594 27 27, g32p_row02_traceSegment_015_0594_0027, g32p_row02_traceSegment_015_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 540 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 540 54 54, g32p_row02_traceSegment_015_0540_0054, g32p_row02_traceSegment_015_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 432 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 432 108 108, g32p_row02_traceSegment_015_0432_0108, g32p_row02_traceSegment_015_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 648 13 14, g32p_row02_traceSegment_015_0648_0013, g32p_row02_traceSegment_015_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 688 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 675 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 675 13 14, g32p_row02_traceSegment_015_0675_0013, g32p_row02_traceSegment_015_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 648 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 648 27 27, g32p_row02_traceSegment_015_0648_0027, g32p_row02_traceSegment_015_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 702 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 702 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 702 13 14, g32p_row02_traceSegment_015_0702_0013, g32p_row02_traceSegment_015_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 729 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 729 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 729 13 14, g32p_row02_traceSegment_015_0729_0013, g32p_row02_traceSegment_015_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 702 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 702 27 27, g32p_row02_traceSegment_015_0702_0027, g32p_row02_traceSegment_015_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 648 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 648 54 54, g32p_row02_traceSegment_015_0648_0054, g32p_row02_traceSegment_015_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 756 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 756 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 756 13 14, g32p_row02_traceSegment_015_0756_0013, g32p_row02_traceSegment_015_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 796 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 783 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 783 13 14, g32p_row02_traceSegment_015_0783_0013, g32p_row02_traceSegment_015_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 756 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 756 27 27, g32p_row02_traceSegment_015_0756_0027, g32p_row02_traceSegment_015_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 810 13 14, g32p_row02_traceSegment_015_0810_0013, g32p_row02_traceSegment_015_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 837 13 14, g32p_row02_traceSegment_015_0837_0013, g32p_row02_traceSegment_015_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 810 27 27, g32p_row02_traceSegment_015_0810_0027, g32p_row02_traceSegment_015_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 756 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 756 54 54, g32p_row02_traceSegment_015_0756_0054, g32p_row02_traceSegment_015_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 648 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 648 108 108, g32p_row02_traceSegment_015_0648_0108, g32p_row02_traceSegment_015_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_015 432 432 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 432 216 216, g32p_row02_traceSegment_015_0432_0216, g32p_row02_traceSegment_015_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_015 0 864 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 0 432 432, g32p_row02_traceSegment_015_0000_0432, g32p_row02_traceSegment_015_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 864 13 14, g32p_row02_traceSegment_015_0864_0013, g32p_row02_traceSegment_015_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 891 13 14, g32p_row02_traceSegment_015_0891_0013, g32p_row02_traceSegment_015_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 864 27 27, g32p_row02_traceSegment_015_0864_0027, g32p_row02_traceSegment_015_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 918 13 14, g32p_row02_traceSegment_015_0918_0013, g32p_row02_traceSegment_015_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 945 13 14, g32p_row02_traceSegment_015_0945_0013, g32p_row02_traceSegment_015_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 918 27 27, g32p_row02_traceSegment_015_0918_0027, g32p_row02_traceSegment_015_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 864 54 54, g32p_row02_traceSegment_015_0864_0054, g32p_row02_traceSegment_015_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 972 13 14, g32p_row02_traceSegment_015_0972_0013, g32p_row02_traceSegment_015_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 999 13 14, g32p_row02_traceSegment_015_0999_0013, g32p_row02_traceSegment_015_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 972 27 27, g32p_row02_traceSegment_015_0972_0027, g32p_row02_traceSegment_015_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1026 13 14, g32p_row02_traceSegment_015_1026_0013, g32p_row02_traceSegment_015_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1053 13 14, g32p_row02_traceSegment_015_1053_0013, g32p_row02_traceSegment_015_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1026 27 27, g32p_row02_traceSegment_015_1026_0027, g32p_row02_traceSegment_015_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 972 54 54, g32p_row02_traceSegment_015_0972_0054, g32p_row02_traceSegment_015_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 864 108 108, g32p_row02_traceSegment_015_0864_0108, g32p_row02_traceSegment_015_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1080 13 14, g32p_row02_traceSegment_015_1080_0013, g32p_row02_traceSegment_015_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1107 13 14, g32p_row02_traceSegment_015_1107_0013, g32p_row02_traceSegment_015_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1080 27 27, g32p_row02_traceSegment_015_1080_0027, g32p_row02_traceSegment_015_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1134 13 14, g32p_row02_traceSegment_015_1134_0013, g32p_row02_traceSegment_015_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1161 13 14, g32p_row02_traceSegment_015_1161_0013, g32p_row02_traceSegment_015_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1134 27 27, g32p_row02_traceSegment_015_1134_0027, g32p_row02_traceSegment_015_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1080 54 54, g32p_row02_traceSegment_015_1080_0054, g32p_row02_traceSegment_015_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1188 13 14, g32p_row02_traceSegment_015_1188_0013, g32p_row02_traceSegment_015_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1215 13 14, g32p_row02_traceSegment_015_1215_0013, g32p_row02_traceSegment_015_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1188 27 27, g32p_row02_traceSegment_015_1188_0027, g32p_row02_traceSegment_015_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1242 13 14, g32p_row02_traceSegment_015_1242_0013, g32p_row02_traceSegment_015_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1269 13 14, g32p_row02_traceSegment_015_1269_0013, g32p_row02_traceSegment_015_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1242 27 27, g32p_row02_traceSegment_015_1242_0027, g32p_row02_traceSegment_015_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1188 54 54, g32p_row02_traceSegment_015_1188_0054, g32p_row02_traceSegment_015_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1080 108 108, g32p_row02_traceSegment_015_1080_0108, g32p_row02_traceSegment_015_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_015 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 864 216 216, g32p_row02_traceSegment_015_0864_0216, g32p_row02_traceSegment_015_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1296 13 14, g32p_row02_traceSegment_015_1296_0013, g32p_row02_traceSegment_015_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1323 13 14, g32p_row02_traceSegment_015_1323_0013, g32p_row02_traceSegment_015_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1296 27 27, g32p_row02_traceSegment_015_1296_0027, g32p_row02_traceSegment_015_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1350 13 14, g32p_row02_traceSegment_015_1350_0013, g32p_row02_traceSegment_015_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1377 13 14, g32p_row02_traceSegment_015_1377_0013, g32p_row02_traceSegment_015_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1350 27 27, g32p_row02_traceSegment_015_1350_0027, g32p_row02_traceSegment_015_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1296 54 54, g32p_row02_traceSegment_015_1296_0054, g32p_row02_traceSegment_015_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1404 13 14, g32p_row02_traceSegment_015_1404_0013, g32p_row02_traceSegment_015_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1431 13 14, g32p_row02_traceSegment_015_1431_0013, g32p_row02_traceSegment_015_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1404 27 27, g32p_row02_traceSegment_015_1404_0027, g32p_row02_traceSegment_015_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1458 13 14, g32p_row02_traceSegment_015_1458_0013, g32p_row02_traceSegment_015_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1485 13 14, g32p_row02_traceSegment_015_1485_0013, g32p_row02_traceSegment_015_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1458 27 27, g32p_row02_traceSegment_015_1458_0027, g32p_row02_traceSegment_015_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1404 54 54, g32p_row02_traceSegment_015_1404_0054, g32p_row02_traceSegment_015_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1296 108 108, g32p_row02_traceSegment_015_1296_0108, g32p_row02_traceSegment_015_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1512 13 14, g32p_row02_traceSegment_015_1512_0013, g32p_row02_traceSegment_015_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1539 13 14, g32p_row02_traceSegment_015_1539_0013, g32p_row02_traceSegment_015_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1512 27 27, g32p_row02_traceSegment_015_1512_0027, g32p_row02_traceSegment_015_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1566 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1566 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1566 13 14, g32p_row02_traceSegment_015_1566_0013, g32p_row02_traceSegment_015_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1606 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1593 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1593 13 14, g32p_row02_traceSegment_015_1593_0013, g32p_row02_traceSegment_015_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1566 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1566 27 27, g32p_row02_traceSegment_015_1566_0027, g32p_row02_traceSegment_015_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 1512 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1512 54 54, g32p_row02_traceSegment_015_1512_0054, g32p_row02_traceSegment_015_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1620 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1620 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1620 13 14, g32p_row02_traceSegment_015_1620_0013, g32p_row02_traceSegment_015_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1647 13 14, g32p_row02_traceSegment_015_1647_0013, g32p_row02_traceSegment_015_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1620 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1620 27 27, g32p_row02_traceSegment_015_1620_0027, g32p_row02_traceSegment_015_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1674 13 14, g32p_row02_traceSegment_015_1674_0013, g32p_row02_traceSegment_015_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1701 13 14, g32p_row02_traceSegment_015_1701_0013, g32p_row02_traceSegment_015_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1674 27 27, g32p_row02_traceSegment_015_1674_0027, g32p_row02_traceSegment_015_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 1620 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1620 54 54, g32p_row02_traceSegment_015_1620_0054, g32p_row02_traceSegment_015_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 1512 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1512 108 108, g32p_row02_traceSegment_015_1512_0108, g32p_row02_traceSegment_015_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_015 1296 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1296 216 216, g32p_row02_traceSegment_015_1296_0216, g32p_row02_traceSegment_015_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_015 864 864 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 864 432 432, g32p_row02_traceSegment_015_0864_0432, g32p_row02_traceSegment_015_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_015 0 1728 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 0 864 864, g32p_row02_traceSegment_015_0000_0864, g32p_row02_traceSegment_015_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1728 13 14, g32p_row02_traceSegment_015_1728_0013, g32p_row02_traceSegment_015_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1755 13 14, g32p_row02_traceSegment_015_1755_0013, g32p_row02_traceSegment_015_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1728 27 27, g32p_row02_traceSegment_015_1728_0027, g32p_row02_traceSegment_015_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1795 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1782 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1782 13 14, g32p_row02_traceSegment_015_1782_0013, g32p_row02_traceSegment_015_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1809 13 14, g32p_row02_traceSegment_015_1809_0013, g32p_row02_traceSegment_015_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1782 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1782 27 27, g32p_row02_traceSegment_015_1782_0027, g32p_row02_traceSegment_015_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 1728 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1728 54 54, g32p_row02_traceSegment_015_1728_0054, g32p_row02_traceSegment_015_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1836 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1836 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1836 13 14, g32p_row02_traceSegment_015_1836_0013, g32p_row02_traceSegment_015_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1876 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1863 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1863 13 14, g32p_row02_traceSegment_015_1863_0013, g32p_row02_traceSegment_015_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1836 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1836 27 27, g32p_row02_traceSegment_015_1836_0027, g32p_row02_traceSegment_015_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1890 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1890 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1890 13 14, g32p_row02_traceSegment_015_1890_0013, g32p_row02_traceSegment_015_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1917 13 14, g32p_row02_traceSegment_015_1917_0013, g32p_row02_traceSegment_015_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1890 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1890 27 27, g32p_row02_traceSegment_015_1890_0027, g32p_row02_traceSegment_015_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 1836 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1836 54 54, g32p_row02_traceSegment_015_1836_0054, g32p_row02_traceSegment_015_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 1728 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1728 108 108, g32p_row02_traceSegment_015_1728_0108, g32p_row02_traceSegment_015_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1944 13 14, g32p_row02_traceSegment_015_1944_0013, g32p_row02_traceSegment_015_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1971 13 14, g32p_row02_traceSegment_015_1971_0013, g32p_row02_traceSegment_015_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1944 27 27, g32p_row02_traceSegment_015_1944_0027, g32p_row02_traceSegment_015_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1998 13 14, g32p_row02_traceSegment_015_1998_0013, g32p_row02_traceSegment_015_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2025 13 14, g32p_row02_traceSegment_015_2025_0013, g32p_row02_traceSegment_015_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1998 27 27, g32p_row02_traceSegment_015_1998_0027, g32p_row02_traceSegment_015_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1944 54 54, g32p_row02_traceSegment_015_1944_0054, g32p_row02_traceSegment_015_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2052 13 14, g32p_row02_traceSegment_015_2052_0013, g32p_row02_traceSegment_015_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2079 13 14, g32p_row02_traceSegment_015_2079_0013, g32p_row02_traceSegment_015_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2052 27 27, g32p_row02_traceSegment_015_2052_0027, g32p_row02_traceSegment_015_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2106 13 14, g32p_row02_traceSegment_015_2106_0013, g32p_row02_traceSegment_015_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2133 13 14, g32p_row02_traceSegment_015_2133_0013, g32p_row02_traceSegment_015_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2106 27 27, g32p_row02_traceSegment_015_2106_0027, g32p_row02_traceSegment_015_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2052 54 54, g32p_row02_traceSegment_015_2052_0054, g32p_row02_traceSegment_015_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1944 108 108, g32p_row02_traceSegment_015_1944_0108, g32p_row02_traceSegment_015_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_015 1728 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1728 216 216, g32p_row02_traceSegment_015_1728_0216, g32p_row02_traceSegment_015_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2160 13 14, g32p_row02_traceSegment_015_2160_0013, g32p_row02_traceSegment_015_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2187 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2200 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2187 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2187 13 14, g32p_row02_traceSegment_015_2187_0013, g32p_row02_traceSegment_015_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2160 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2160 27 27, g32p_row02_traceSegment_015_2160_0027, g32p_row02_traceSegment_015_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2214 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2214 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2214 13 14, g32p_row02_traceSegment_015_2214_0013, g32p_row02_traceSegment_015_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2241 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2241 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2241 13 14, g32p_row02_traceSegment_015_2241_0013, g32p_row02_traceSegment_015_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2214 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2214 27 27, g32p_row02_traceSegment_015_2214_0027, g32p_row02_traceSegment_015_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 2160 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2160 54 54, g32p_row02_traceSegment_015_2160_0054, g32p_row02_traceSegment_015_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2268 13 14, g32p_row02_traceSegment_015_2268_0013, g32p_row02_traceSegment_015_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2295 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2295 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2295 13 14, g32p_row02_traceSegment_015_2295_0013, g32p_row02_traceSegment_015_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2268 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2268 27 27, g32p_row02_traceSegment_015_2268_0027, g32p_row02_traceSegment_015_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2322 13 14, g32p_row02_traceSegment_015_2322_0013, g32p_row02_traceSegment_015_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2349 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2349 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2349 13 14, g32p_row02_traceSegment_015_2349_0013, g32p_row02_traceSegment_015_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2322 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2322 27 27, g32p_row02_traceSegment_015_2322_0027, g32p_row02_traceSegment_015_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 2268 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2268 54 54, g32p_row02_traceSegment_015_2268_0054, g32p_row02_traceSegment_015_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 2160 216 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2160 108 108, g32p_row02_traceSegment_015_2160_0108, g32p_row02_traceSegment_015_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2376 13 14, g32p_row02_traceSegment_015_2376_0013, g32p_row02_traceSegment_015_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2403 13 14, g32p_row02_traceSegment_015_2403_0013, g32p_row02_traceSegment_015_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2376 27 27, g32p_row02_traceSegment_015_2376_0027, g32p_row02_traceSegment_015_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2430 13 14, g32p_row02_traceSegment_015_2430_0013, g32p_row02_traceSegment_015_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2457 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2470 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2457 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2457 13 14, g32p_row02_traceSegment_015_2457_0013, g32p_row02_traceSegment_015_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2430 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2430 27 27, g32p_row02_traceSegment_015_2430_0027, g32p_row02_traceSegment_015_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 2376 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2376 54 54, g32p_row02_traceSegment_015_2376_0054, g32p_row02_traceSegment_015_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2484 13 14, g32p_row02_traceSegment_015_2484_0013, g32p_row02_traceSegment_015_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2511 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2511 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2511 13 14, g32p_row02_traceSegment_015_2511_0013, g32p_row02_traceSegment_015_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2484 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2484 27 27, g32p_row02_traceSegment_015_2484_0027, g32p_row02_traceSegment_015_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2538 13 14, g32p_row02_traceSegment_015_2538_0013, g32p_row02_traceSegment_015_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2565 13 14, g32p_row02_traceSegment_015_2565_0013, g32p_row02_traceSegment_015_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2538 27 27, g32p_row02_traceSegment_015_2538_0027, g32p_row02_traceSegment_015_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 2484 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2484 54 54, g32p_row02_traceSegment_015_2484_0054, g32p_row02_traceSegment_015_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 2376 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2376 108 108, g32p_row02_traceSegment_015_2376_0108, g32p_row02_traceSegment_015_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_015 2160 432 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2160 216 216, g32p_row02_traceSegment_015_2160_0216, g32p_row02_traceSegment_015_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_015 1728 864 = [0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1728 432 432, g32p_row02_traceSegment_015_1728_0432, g32p_row02_traceSegment_015_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2592 13 14, g32p_row02_traceSegment_015_2592_0013, g32p_row02_traceSegment_015_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2619 13 14, g32p_row02_traceSegment_015_2619_0013, g32p_row02_traceSegment_015_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2592 27 27, g32p_row02_traceSegment_015_2592_0027, g32p_row02_traceSegment_015_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2646 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2646 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2646 13 14, g32p_row02_traceSegment_015_2646_0013, g32p_row02_traceSegment_015_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2673 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2673 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2673 13 14, g32p_row02_traceSegment_015_2673_0013, g32p_row02_traceSegment_015_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2646 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2646 27 27, g32p_row02_traceSegment_015_2646_0027, g32p_row02_traceSegment_015_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 2592 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2592 54 54, g32p_row02_traceSegment_015_2592_0054, g32p_row02_traceSegment_015_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2700 13 14, g32p_row02_traceSegment_015_2700_0013, g32p_row02_traceSegment_015_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2740 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2727 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2727 13 14, g32p_row02_traceSegment_015_2727_0013, g32p_row02_traceSegment_015_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2700 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2700 27 27, g32p_row02_traceSegment_015_2700_0027, g32p_row02_traceSegment_015_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2754 13 14, g32p_row02_traceSegment_015_2754_0013, g32p_row02_traceSegment_015_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2781 13 14, g32p_row02_traceSegment_015_2781_0013, g32p_row02_traceSegment_015_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2754 27 27, g32p_row02_traceSegment_015_2754_0027, g32p_row02_traceSegment_015_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 2700 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2700 54 54, g32p_row02_traceSegment_015_2700_0054, g32p_row02_traceSegment_015_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 2592 216 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2592 108 108, g32p_row02_traceSegment_015_2592_0108, g32p_row02_traceSegment_015_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2821 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2808 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2808 13 14, g32p_row02_traceSegment_015_2808_0013, g32p_row02_traceSegment_015_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2835 13 14, g32p_row02_traceSegment_015_2835_0013, g32p_row02_traceSegment_015_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2808 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2808 27 27, g32p_row02_traceSegment_015_2808_0027, g32p_row02_traceSegment_015_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2862 13 14, g32p_row02_traceSegment_015_2862_0013, g32p_row02_traceSegment_015_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2889 13 14, g32p_row02_traceSegment_015_2889_0013, g32p_row02_traceSegment_015_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2862 27 27, g32p_row02_traceSegment_015_2862_0027, g32p_row02_traceSegment_015_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 2808 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2808 54 54, g32p_row02_traceSegment_015_2808_0054, g32p_row02_traceSegment_015_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2916 13 14, g32p_row02_traceSegment_015_2916_0013, g32p_row02_traceSegment_015_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2943 13 14, g32p_row02_traceSegment_015_2943_0013, g32p_row02_traceSegment_015_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2916 27 27, g32p_row02_traceSegment_015_2916_0027, g32p_row02_traceSegment_015_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2970 13 14, g32p_row02_traceSegment_015_2970_0013, g32p_row02_traceSegment_015_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2997 13 14, g32p_row02_traceSegment_015_2997_0013, g32p_row02_traceSegment_015_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2970 27 27, g32p_row02_traceSegment_015_2970_0027, g32p_row02_traceSegment_015_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2916 54 54, g32p_row02_traceSegment_015_2916_0054, g32p_row02_traceSegment_015_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 2808 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2808 108 108, g32p_row02_traceSegment_015_2808_0108, g32p_row02_traceSegment_015_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_015 2592 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2592 216 216, g32p_row02_traceSegment_015_2592_0216, g32p_row02_traceSegment_015_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3024 13 14, g32p_row02_traceSegment_015_3024_0013, g32p_row02_traceSegment_015_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3051 13 14, g32p_row02_traceSegment_015_3051_0013, g32p_row02_traceSegment_015_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3024 27 27, g32p_row02_traceSegment_015_3024_0027, g32p_row02_traceSegment_015_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3078 13 14, g32p_row02_traceSegment_015_3078_0013, g32p_row02_traceSegment_015_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3105 13 14, g32p_row02_traceSegment_015_3105_0013, g32p_row02_traceSegment_015_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3078 27 27, g32p_row02_traceSegment_015_3078_0027, g32p_row02_traceSegment_015_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3024 54 54, g32p_row02_traceSegment_015_3024_0054, g32p_row02_traceSegment_015_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3132 13 14, g32p_row02_traceSegment_015_3132_0013, g32p_row02_traceSegment_015_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3159 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3159 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3159 13 14, g32p_row02_traceSegment_015_3159_0013, g32p_row02_traceSegment_015_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 3132 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3132 27 27, g32p_row02_traceSegment_015_3132_0027, g32p_row02_traceSegment_015_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3199 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3186 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3186 13 14, g32p_row02_traceSegment_015_3186_0013, g32p_row02_traceSegment_015_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3213 13 14, g32p_row02_traceSegment_015_3213_0013, g32p_row02_traceSegment_015_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 3186 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3186 27 27, g32p_row02_traceSegment_015_3186_0027, g32p_row02_traceSegment_015_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 3132 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3132 54 54, g32p_row02_traceSegment_015_3132_0054, g32p_row02_traceSegment_015_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 3024 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3024 108 108, g32p_row02_traceSegment_015_3024_0108, g32p_row02_traceSegment_015_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3240 13 14, g32p_row02_traceSegment_015_3240_0013, g32p_row02_traceSegment_015_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3267 13 14, g32p_row02_traceSegment_015_3267_0013, g32p_row02_traceSegment_015_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3240 27 27, g32p_row02_traceSegment_015_3240_0027, g32p_row02_traceSegment_015_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3294 13 14, g32p_row02_traceSegment_015_3294_0013, g32p_row02_traceSegment_015_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3321 13 14, g32p_row02_traceSegment_015_3321_0013, g32p_row02_traceSegment_015_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3294 27 27, g32p_row02_traceSegment_015_3294_0027, g32p_row02_traceSegment_015_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3240 54 54, g32p_row02_traceSegment_015_3240_0054, g32p_row02_traceSegment_015_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3348 13 14, g32p_row02_traceSegment_015_3348_0013, g32p_row02_traceSegment_015_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3375 13 14, g32p_row02_traceSegment_015_3375_0013, g32p_row02_traceSegment_015_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3348 27 27, g32p_row02_traceSegment_015_3348_0027, g32p_row02_traceSegment_015_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3402 13 14, g32p_row02_traceSegment_015_3402_0013, g32p_row02_traceSegment_015_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_015 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_015 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_015_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_015 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3429 13 14, g32p_row02_traceSegment_015_3429_0013, g32p_row02_traceSegment_015_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_015 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3402 27 27, g32p_row02_traceSegment_015_3402_0027, g32p_row02_traceSegment_015_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_015 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3348 54 54, g32p_row02_traceSegment_015_3348_0054, g32p_row02_traceSegment_015_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_015 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3240 108 108, g32p_row02_traceSegment_015_3240_0108, g32p_row02_traceSegment_015_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_015_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_015 3024 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 3024 216 216, g32p_row02_traceSegment_015_3024_0216, g32p_row02_traceSegment_015_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_015_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_015 2592 864 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 2592 432 432, g32p_row02_traceSegment_015_2592_0432, g32p_row02_traceSegment_015_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_015_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_015 1728 1728 = [0, 0, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 1728 864 864, g32p_row02_traceSegment_015_1728_0864, g32p_row02_traceSegment_015_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_015_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_015 0 3456 = [0, 0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_015 0 1728 1728, g32p_row02_traceSegment_015_0000_1728, g32p_row02_traceSegment_015_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 15 = [0, 0, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_015_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_017 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 17 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_017_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 0 13 14, g32p_row02_traceSegment_017_0000_0013, g32p_row02_traceSegment_017_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 27 13 14, g32p_row02_traceSegment_017_0027_0013, g32p_row02_traceSegment_017_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 0 27 27, g32p_row02_traceSegment_017_0000_0027, g32p_row02_traceSegment_017_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 54 13 14, g32p_row02_traceSegment_017_0054_0013, g32p_row02_traceSegment_017_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 81 13 14, g32p_row02_traceSegment_017_0081_0013, g32p_row02_traceSegment_017_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 54 27 27, g32p_row02_traceSegment_017_0054_0027, g32p_row02_traceSegment_017_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 0 54 54, g32p_row02_traceSegment_017_0000_0054, g32p_row02_traceSegment_017_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 108 13 14, g32p_row02_traceSegment_017_0108_0013, g32p_row02_traceSegment_017_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 135 13 14, g32p_row02_traceSegment_017_0135_0013, g32p_row02_traceSegment_017_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 108 27 27, g32p_row02_traceSegment_017_0108_0027, g32p_row02_traceSegment_017_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 162 13 14, g32p_row02_traceSegment_017_0162_0013, g32p_row02_traceSegment_017_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 189 13 14, g32p_row02_traceSegment_017_0189_0013, g32p_row02_traceSegment_017_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 162 27 27, g32p_row02_traceSegment_017_0162_0027, g32p_row02_traceSegment_017_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 108 54 54, g32p_row02_traceSegment_017_0108_0054, g32p_row02_traceSegment_017_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 0 108 108, g32p_row02_traceSegment_017_0000_0108, g32p_row02_traceSegment_017_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 216 13 14, g32p_row02_traceSegment_017_0216_0013, g32p_row02_traceSegment_017_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 243 13 14, g32p_row02_traceSegment_017_0243_0013, g32p_row02_traceSegment_017_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 216 27 27, g32p_row02_traceSegment_017_0216_0027, g32p_row02_traceSegment_017_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 270 13 14, g32p_row02_traceSegment_017_0270_0013, g32p_row02_traceSegment_017_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 297 13 14, g32p_row02_traceSegment_017_0297_0013, g32p_row02_traceSegment_017_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 270 27 27, g32p_row02_traceSegment_017_0270_0027, g32p_row02_traceSegment_017_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 216 54 54, g32p_row02_traceSegment_017_0216_0054, g32p_row02_traceSegment_017_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 324 13 14, g32p_row02_traceSegment_017_0324_0013, g32p_row02_traceSegment_017_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 351 13 14, g32p_row02_traceSegment_017_0351_0013, g32p_row02_traceSegment_017_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 324 27 27, g32p_row02_traceSegment_017_0324_0027, g32p_row02_traceSegment_017_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 378 13 14, g32p_row02_traceSegment_017_0378_0013, g32p_row02_traceSegment_017_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 405 13 14, g32p_row02_traceSegment_017_0405_0013, g32p_row02_traceSegment_017_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 378 27 27, g32p_row02_traceSegment_017_0378_0027, g32p_row02_traceSegment_017_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 324 54 54, g32p_row02_traceSegment_017_0324_0054, g32p_row02_traceSegment_017_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 216 108 108, g32p_row02_traceSegment_017_0216_0108, g32p_row02_traceSegment_017_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_017 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 0 216 216, g32p_row02_traceSegment_017_0000_0216, g32p_row02_traceSegment_017_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 432 13 14, g32p_row02_traceSegment_017_0432_0013, g32p_row02_traceSegment_017_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 459 13 14, g32p_row02_traceSegment_017_0459_0013, g32p_row02_traceSegment_017_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 432 27 27, g32p_row02_traceSegment_017_0432_0027, g32p_row02_traceSegment_017_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 499 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 486 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 486 13 14, g32p_row02_traceSegment_017_0486_0013, g32p_row02_traceSegment_017_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 513 13 14, g32p_row02_traceSegment_017_0513_0013, g32p_row02_traceSegment_017_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 486 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 486 27 27, g32p_row02_traceSegment_017_0486_0027, g32p_row02_traceSegment_017_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 432 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 432 54 54, g32p_row02_traceSegment_017_0432_0054, g32p_row02_traceSegment_017_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 540 13 14, g32p_row02_traceSegment_017_0540_0013, g32p_row02_traceSegment_017_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 567 13 14, g32p_row02_traceSegment_017_0567_0013, g32p_row02_traceSegment_017_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 540 27 27, g32p_row02_traceSegment_017_0540_0027, g32p_row02_traceSegment_017_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 594 13 14, g32p_row02_traceSegment_017_0594_0013, g32p_row02_traceSegment_017_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 621 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 634 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 621 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 621 13 14, g32p_row02_traceSegment_017_0621_0013, g32p_row02_traceSegment_017_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 594 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 594 27 27, g32p_row02_traceSegment_017_0594_0027, g32p_row02_traceSegment_017_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 540 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 540 54 54, g32p_row02_traceSegment_017_0540_0054, g32p_row02_traceSegment_017_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 432 216 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 432 108 108, g32p_row02_traceSegment_017_0432_0108, g32p_row02_traceSegment_017_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 648 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 661 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 648 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 648 13 14, g32p_row02_traceSegment_017_0648_0013, g32p_row02_traceSegment_017_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 675 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 675 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 675 13 14, g32p_row02_traceSegment_017_0675_0013, g32p_row02_traceSegment_017_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 648 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 648 27 27, g32p_row02_traceSegment_017_0648_0027, g32p_row02_traceSegment_017_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 702 13 14, g32p_row02_traceSegment_017_0702_0013, g32p_row02_traceSegment_017_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 729 13 14, g32p_row02_traceSegment_017_0729_0013, g32p_row02_traceSegment_017_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 702 27 27, g32p_row02_traceSegment_017_0702_0027, g32p_row02_traceSegment_017_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 648 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 648 54 54, g32p_row02_traceSegment_017_0648_0054, g32p_row02_traceSegment_017_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 756 13 14, g32p_row02_traceSegment_017_0756_0013, g32p_row02_traceSegment_017_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 783 13 14, g32p_row02_traceSegment_017_0783_0013, g32p_row02_traceSegment_017_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 756 27 27, g32p_row02_traceSegment_017_0756_0027, g32p_row02_traceSegment_017_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 810 13 14, g32p_row02_traceSegment_017_0810_0013, g32p_row02_traceSegment_017_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 837 13 14, g32p_row02_traceSegment_017_0837_0013, g32p_row02_traceSegment_017_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 810 27 27, g32p_row02_traceSegment_017_0810_0027, g32p_row02_traceSegment_017_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 756 54 54, g32p_row02_traceSegment_017_0756_0054, g32p_row02_traceSegment_017_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 648 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 648 108 108, g32p_row02_traceSegment_017_0648_0108, g32p_row02_traceSegment_017_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_017 432 432 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 432 216 216, g32p_row02_traceSegment_017_0432_0216, g32p_row02_traceSegment_017_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_017 0 864 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 0 432 432, g32p_row02_traceSegment_017_0000_0432, g32p_row02_traceSegment_017_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 864 13 14, g32p_row02_traceSegment_017_0864_0013, g32p_row02_traceSegment_017_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 891 13 14, g32p_row02_traceSegment_017_0891_0013, g32p_row02_traceSegment_017_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 864 27 27, g32p_row02_traceSegment_017_0864_0027, g32p_row02_traceSegment_017_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 918 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 931 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 918 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 918 13 14, g32p_row02_traceSegment_017_0918_0013, g32p_row02_traceSegment_017_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 945 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 958 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 945 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 945 13 14, g32p_row02_traceSegment_017_0945_0013, g32p_row02_traceSegment_017_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 918 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 918 27 27, g32p_row02_traceSegment_017_0918_0027, g32p_row02_traceSegment_017_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 864 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 864 54 54, g32p_row02_traceSegment_017_0864_0054, g32p_row02_traceSegment_017_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 985 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 972 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 972 13 14, g32p_row02_traceSegment_017_0972_0013, g32p_row02_traceSegment_017_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 999 13 14, g32p_row02_traceSegment_017_0999_0013, g32p_row02_traceSegment_017_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 972 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 972 27 27, g32p_row02_traceSegment_017_0972_0027, g32p_row02_traceSegment_017_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1026 13 14, g32p_row02_traceSegment_017_1026_0013, g32p_row02_traceSegment_017_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1053 13 14, g32p_row02_traceSegment_017_1053_0013, g32p_row02_traceSegment_017_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1026 27 27, g32p_row02_traceSegment_017_1026_0027, g32p_row02_traceSegment_017_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 972 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 972 54 54, g32p_row02_traceSegment_017_0972_0054, g32p_row02_traceSegment_017_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 864 216 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 864 108 108, g32p_row02_traceSegment_017_0864_0108, g32p_row02_traceSegment_017_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1080 13 14, g32p_row02_traceSegment_017_1080_0013, g32p_row02_traceSegment_017_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1120 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1107 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1107 13 14, g32p_row02_traceSegment_017_1107_0013, g32p_row02_traceSegment_017_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1080 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1080 27 27, g32p_row02_traceSegment_017_1080_0027, g32p_row02_traceSegment_017_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1134 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1147 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1134 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1134 13 14, g32p_row02_traceSegment_017_1134_0013, g32p_row02_traceSegment_017_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1161 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1174 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1161 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1161 13 14, g32p_row02_traceSegment_017_1161_0013, g32p_row02_traceSegment_017_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1134 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1134 27 27, g32p_row02_traceSegment_017_1134_0027, g32p_row02_traceSegment_017_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 1080 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1080 54 54, g32p_row02_traceSegment_017_1080_0054, g32p_row02_traceSegment_017_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1188 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1188 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1188 13 14, g32p_row02_traceSegment_017_1188_0013, g32p_row02_traceSegment_017_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1228 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1215 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1215 13 14, g32p_row02_traceSegment_017_1215_0013, g32p_row02_traceSegment_017_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1188 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1188 27 27, g32p_row02_traceSegment_017_1188_0027, g32p_row02_traceSegment_017_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1242 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1255 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1242 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1242 13 14, g32p_row02_traceSegment_017_1242_0013, g32p_row02_traceSegment_017_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1269 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1282 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1269 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1269 13 14, g32p_row02_traceSegment_017_1269_0013, g32p_row02_traceSegment_017_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1242 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1242 27 27, g32p_row02_traceSegment_017_1242_0027, g32p_row02_traceSegment_017_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 1188 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1188 54 54, g32p_row02_traceSegment_017_1188_0054, g32p_row02_traceSegment_017_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 1080 216 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1080 108 108, g32p_row02_traceSegment_017_1080_0108, g32p_row02_traceSegment_017_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_017 864 432 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 864 216 216, g32p_row02_traceSegment_017_0864_0216, g32p_row02_traceSegment_017_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1296 13 14, g32p_row02_traceSegment_017_1296_0013, g32p_row02_traceSegment_017_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1323 13 14, g32p_row02_traceSegment_017_1323_0013, g32p_row02_traceSegment_017_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1296 27 27, g32p_row02_traceSegment_017_1296_0027, g32p_row02_traceSegment_017_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1350 13 14, g32p_row02_traceSegment_017_1350_0013, g32p_row02_traceSegment_017_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1377 13 14, g32p_row02_traceSegment_017_1377_0013, g32p_row02_traceSegment_017_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1350 27 27, g32p_row02_traceSegment_017_1350_0027, g32p_row02_traceSegment_017_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1296 54 54, g32p_row02_traceSegment_017_1296_0054, g32p_row02_traceSegment_017_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1404 13 14, g32p_row02_traceSegment_017_1404_0013, g32p_row02_traceSegment_017_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1431 13 14, g32p_row02_traceSegment_017_1431_0013, g32p_row02_traceSegment_017_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1404 27 27, g32p_row02_traceSegment_017_1404_0027, g32p_row02_traceSegment_017_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1458 13 14, g32p_row02_traceSegment_017_1458_0013, g32p_row02_traceSegment_017_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1485 13 14, g32p_row02_traceSegment_017_1485_0013, g32p_row02_traceSegment_017_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1458 27 27, g32p_row02_traceSegment_017_1458_0027, g32p_row02_traceSegment_017_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1404 54 54, g32p_row02_traceSegment_017_1404_0054, g32p_row02_traceSegment_017_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1296 108 108, g32p_row02_traceSegment_017_1296_0108, g32p_row02_traceSegment_017_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1512 13 14, g32p_row02_traceSegment_017_1512_0013, g32p_row02_traceSegment_017_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1552 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1539 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1539 13 14, g32p_row02_traceSegment_017_1539_0013, g32p_row02_traceSegment_017_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1512 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1512 27 27, g32p_row02_traceSegment_017_1512_0027, g32p_row02_traceSegment_017_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1579 14 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1566 27 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1566 13 14, g32p_row02_traceSegment_017_1566_0013, g32p_row02_traceSegment_017_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1593 13 14, g32p_row02_traceSegment_017_1593_0013, g32p_row02_traceSegment_017_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1566 54 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1566 27 27, g32p_row02_traceSegment_017_1566_0027, g32p_row02_traceSegment_017_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 1512 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1512 54 54, g32p_row02_traceSegment_017_1512_0054, g32p_row02_traceSegment_017_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1620 13 14, g32p_row02_traceSegment_017_1620_0013, g32p_row02_traceSegment_017_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1647 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1660 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1647 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1647 13 14, g32p_row02_traceSegment_017_1647_0013, g32p_row02_traceSegment_017_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1620 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1620 27 27, g32p_row02_traceSegment_017_1620_0027, g32p_row02_traceSegment_017_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1674 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1674 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1674 13 14, g32p_row02_traceSegment_017_1674_0013, g32p_row02_traceSegment_017_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1701 13 14, g32p_row02_traceSegment_017_1701_0013, g32p_row02_traceSegment_017_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1674 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1674 27 27, g32p_row02_traceSegment_017_1674_0027, g32p_row02_traceSegment_017_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 1620 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1620 54 54, g32p_row02_traceSegment_017_1620_0054, g32p_row02_traceSegment_017_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 1512 216 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1512 108 108, g32p_row02_traceSegment_017_1512_0108, g32p_row02_traceSegment_017_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_017 1296 432 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1296 216 216, g32p_row02_traceSegment_017_1296_0216, g32p_row02_traceSegment_017_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_017 864 864 = [0, 0, 26] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 864 432 432, g32p_row02_traceSegment_017_0864_0432, g32p_row02_traceSegment_017_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_017 0 1728 = [0, 0, 35] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 0 864 864, g32p_row02_traceSegment_017_0000_0864, g32p_row02_traceSegment_017_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1728 13 14, g32p_row02_traceSegment_017_1728_0013, g32p_row02_traceSegment_017_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1755 13 14, g32p_row02_traceSegment_017_1755_0013, g32p_row02_traceSegment_017_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1728 27 27, g32p_row02_traceSegment_017_1728_0027, g32p_row02_traceSegment_017_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1782 13 14, g32p_row02_traceSegment_017_1782_0013, g32p_row02_traceSegment_017_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1809 13 14, g32p_row02_traceSegment_017_1809_0013, g32p_row02_traceSegment_017_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1782 27 27, g32p_row02_traceSegment_017_1782_0027, g32p_row02_traceSegment_017_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1728 54 54, g32p_row02_traceSegment_017_1728_0054, g32p_row02_traceSegment_017_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1836 13 14, g32p_row02_traceSegment_017_1836_0013, g32p_row02_traceSegment_017_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1863 13 14, g32p_row02_traceSegment_017_1863_0013, g32p_row02_traceSegment_017_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1836 27 27, g32p_row02_traceSegment_017_1836_0027, g32p_row02_traceSegment_017_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1890 13 14, g32p_row02_traceSegment_017_1890_0013, g32p_row02_traceSegment_017_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1917 13 14, g32p_row02_traceSegment_017_1917_0013, g32p_row02_traceSegment_017_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1890 27 27, g32p_row02_traceSegment_017_1890_0027, g32p_row02_traceSegment_017_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1836 54 54, g32p_row02_traceSegment_017_1836_0054, g32p_row02_traceSegment_017_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1728 108 108, g32p_row02_traceSegment_017_1728_0108, g32p_row02_traceSegment_017_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1944 13 14, g32p_row02_traceSegment_017_1944_0013, g32p_row02_traceSegment_017_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1971 13 14, g32p_row02_traceSegment_017_1971_0013, g32p_row02_traceSegment_017_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1944 27 27, g32p_row02_traceSegment_017_1944_0027, g32p_row02_traceSegment_017_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1998 13 14, g32p_row02_traceSegment_017_1998_0013, g32p_row02_traceSegment_017_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2025 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2025 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2025 13 14, g32p_row02_traceSegment_017_2025_0013, g32p_row02_traceSegment_017_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 1998 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1998 27 27, g32p_row02_traceSegment_017_1998_0027, g32p_row02_traceSegment_017_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 1944 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1944 54 54, g32p_row02_traceSegment_017_1944_0054, g32p_row02_traceSegment_017_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2052 13 14, g32p_row02_traceSegment_017_2052_0013, g32p_row02_traceSegment_017_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2079 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2079 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2079 13 14, g32p_row02_traceSegment_017_2079_0013, g32p_row02_traceSegment_017_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2052 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2052 27 27, g32p_row02_traceSegment_017_2052_0027, g32p_row02_traceSegment_017_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2119 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2106 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2106 13 14, g32p_row02_traceSegment_017_2106_0013, g32p_row02_traceSegment_017_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2133 13 14, g32p_row02_traceSegment_017_2133_0013, g32p_row02_traceSegment_017_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2106 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2106 27 27, g32p_row02_traceSegment_017_2106_0027, g32p_row02_traceSegment_017_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 2052 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2052 54 54, g32p_row02_traceSegment_017_2052_0054, g32p_row02_traceSegment_017_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 1944 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1944 108 108, g32p_row02_traceSegment_017_1944_0108, g32p_row02_traceSegment_017_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_017 1728 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1728 216 216, g32p_row02_traceSegment_017_1728_0216, g32p_row02_traceSegment_017_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2173 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2160 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2160 13 14, g32p_row02_traceSegment_017_2160_0013, g32p_row02_traceSegment_017_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2187 13 14, g32p_row02_traceSegment_017_2187_0013, g32p_row02_traceSegment_017_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2160 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2160 27 27, g32p_row02_traceSegment_017_2160_0027, g32p_row02_traceSegment_017_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2214 13 14, g32p_row02_traceSegment_017_2214_0013, g32p_row02_traceSegment_017_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2241 13 14, g32p_row02_traceSegment_017_2241_0013, g32p_row02_traceSegment_017_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2214 27 27, g32p_row02_traceSegment_017_2214_0027, g32p_row02_traceSegment_017_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 2160 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2160 54 54, g32p_row02_traceSegment_017_2160_0054, g32p_row02_traceSegment_017_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2268 13 14, g32p_row02_traceSegment_017_2268_0013, g32p_row02_traceSegment_017_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2295 13 14, g32p_row02_traceSegment_017_2295_0013, g32p_row02_traceSegment_017_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2268 27 27, g32p_row02_traceSegment_017_2268_0027, g32p_row02_traceSegment_017_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2322 13 14, g32p_row02_traceSegment_017_2322_0013, g32p_row02_traceSegment_017_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2349 13 14, g32p_row02_traceSegment_017_2349_0013, g32p_row02_traceSegment_017_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2322 27 27, g32p_row02_traceSegment_017_2322_0027, g32p_row02_traceSegment_017_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2268 54 54, g32p_row02_traceSegment_017_2268_0054, g32p_row02_traceSegment_017_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 2160 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2160 108 108, g32p_row02_traceSegment_017_2160_0108, g32p_row02_traceSegment_017_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2376 13 14, g32p_row02_traceSegment_017_2376_0013, g32p_row02_traceSegment_017_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2403 13 14, g32p_row02_traceSegment_017_2403_0013, g32p_row02_traceSegment_017_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2376 27 27, g32p_row02_traceSegment_017_2376_0027, g32p_row02_traceSegment_017_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2443 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2430 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2430 13 14, g32p_row02_traceSegment_017_2430_0013, g32p_row02_traceSegment_017_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2457 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2457 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2457 13 14, g32p_row02_traceSegment_017_2457_0013, g32p_row02_traceSegment_017_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2430 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2430 27 27, g32p_row02_traceSegment_017_2430_0027, g32p_row02_traceSegment_017_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 2376 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2376 54 54, g32p_row02_traceSegment_017_2376_0054, g32p_row02_traceSegment_017_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2484 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2497 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2484 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2484 13 14, g32p_row02_traceSegment_017_2484_0013, g32p_row02_traceSegment_017_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2511 13 14, g32p_row02_traceSegment_017_2511_0013, g32p_row02_traceSegment_017_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2484 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2484 27 27, g32p_row02_traceSegment_017_2484_0027, g32p_row02_traceSegment_017_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2538 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2538 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2538 13 14, g32p_row02_traceSegment_017_2538_0013, g32p_row02_traceSegment_017_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2565 13 14, g32p_row02_traceSegment_017_2565_0013, g32p_row02_traceSegment_017_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2538 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2538 27 27, g32p_row02_traceSegment_017_2538_0027, g32p_row02_traceSegment_017_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 2484 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2484 54 54, g32p_row02_traceSegment_017_2484_0054, g32p_row02_traceSegment_017_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 2376 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2376 108 108, g32p_row02_traceSegment_017_2376_0108, g32p_row02_traceSegment_017_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_017 2160 432 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2160 216 216, g32p_row02_traceSegment_017_2160_0216, g32p_row02_traceSegment_017_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_017 1728 864 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1728 432 432, g32p_row02_traceSegment_017_1728_0432, g32p_row02_traceSegment_017_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2592 13 14, g32p_row02_traceSegment_017_2592_0013, g32p_row02_traceSegment_017_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2619 13 14, g32p_row02_traceSegment_017_2619_0013, g32p_row02_traceSegment_017_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2592 27 27, g32p_row02_traceSegment_017_2592_0027, g32p_row02_traceSegment_017_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2646 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2646 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2646 13 14, g32p_row02_traceSegment_017_2646_0013, g32p_row02_traceSegment_017_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2673 13 14, g32p_row02_traceSegment_017_2673_0013, g32p_row02_traceSegment_017_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2646 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2646 27 27, g32p_row02_traceSegment_017_2646_0027, g32p_row02_traceSegment_017_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 2592 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2592 54 54, g32p_row02_traceSegment_017_2592_0054, g32p_row02_traceSegment_017_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2700 13 14, g32p_row02_traceSegment_017_2700_0013, g32p_row02_traceSegment_017_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2727 13 14, g32p_row02_traceSegment_017_2727_0013, g32p_row02_traceSegment_017_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2700 27 27, g32p_row02_traceSegment_017_2700_0027, g32p_row02_traceSegment_017_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2754 13 14, g32p_row02_traceSegment_017_2754_0013, g32p_row02_traceSegment_017_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2781 13 14, g32p_row02_traceSegment_017_2781_0013, g32p_row02_traceSegment_017_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2754 27 27, g32p_row02_traceSegment_017_2754_0027, g32p_row02_traceSegment_017_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2700 54 54, g32p_row02_traceSegment_017_2700_0054, g32p_row02_traceSegment_017_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 2592 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2592 108 108, g32p_row02_traceSegment_017_2592_0108, g32p_row02_traceSegment_017_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2808 13 14, g32p_row02_traceSegment_017_2808_0013, g32p_row02_traceSegment_017_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2835 13 14, g32p_row02_traceSegment_017_2835_0013, g32p_row02_traceSegment_017_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2808 27 27, g32p_row02_traceSegment_017_2808_0027, g32p_row02_traceSegment_017_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2862 13 14, g32p_row02_traceSegment_017_2862_0013, g32p_row02_traceSegment_017_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2889 13 14, g32p_row02_traceSegment_017_2889_0013, g32p_row02_traceSegment_017_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2862 27 27, g32p_row02_traceSegment_017_2862_0027, g32p_row02_traceSegment_017_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2808 54 54, g32p_row02_traceSegment_017_2808_0054, g32p_row02_traceSegment_017_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2916 13 14, g32p_row02_traceSegment_017_2916_0013, g32p_row02_traceSegment_017_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2943 13 14, g32p_row02_traceSegment_017_2943_0013, g32p_row02_traceSegment_017_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2916 27 27, g32p_row02_traceSegment_017_2916_0027, g32p_row02_traceSegment_017_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2970 13 14, g32p_row02_traceSegment_017_2970_0013, g32p_row02_traceSegment_017_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2997 13 14, g32p_row02_traceSegment_017_2997_0013, g32p_row02_traceSegment_017_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2970 27 27, g32p_row02_traceSegment_017_2970_0027, g32p_row02_traceSegment_017_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2916 54 54, g32p_row02_traceSegment_017_2916_0054, g32p_row02_traceSegment_017_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2808 108 108, g32p_row02_traceSegment_017_2808_0108, g32p_row02_traceSegment_017_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_017 2592 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2592 216 216, g32p_row02_traceSegment_017_2592_0216, g32p_row02_traceSegment_017_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3024 13 14, g32p_row02_traceSegment_017_3024_0013, g32p_row02_traceSegment_017_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3051 13 14, g32p_row02_traceSegment_017_3051_0013, g32p_row02_traceSegment_017_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3024 27 27, g32p_row02_traceSegment_017_3024_0027, g32p_row02_traceSegment_017_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3078 13 14, g32p_row02_traceSegment_017_3078_0013, g32p_row02_traceSegment_017_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3105 13 14, g32p_row02_traceSegment_017_3105_0013, g32p_row02_traceSegment_017_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3078 27 27, g32p_row02_traceSegment_017_3078_0027, g32p_row02_traceSegment_017_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3024 54 54, g32p_row02_traceSegment_017_3024_0054, g32p_row02_traceSegment_017_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3132 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3145 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3132 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3132 13 14, g32p_row02_traceSegment_017_3132_0013, g32p_row02_traceSegment_017_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3159 13 14, g32p_row02_traceSegment_017_3159_0013, g32p_row02_traceSegment_017_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 3132 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3132 27 27, g32p_row02_traceSegment_017_3132_0027, g32p_row02_traceSegment_017_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3186 13 14, g32p_row02_traceSegment_017_3186_0013, g32p_row02_traceSegment_017_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3213 13 14, g32p_row02_traceSegment_017_3213_0013, g32p_row02_traceSegment_017_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3186 27 27, g32p_row02_traceSegment_017_3186_0027, g32p_row02_traceSegment_017_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 3132 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3132 54 54, g32p_row02_traceSegment_017_3132_0054, g32p_row02_traceSegment_017_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 3024 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3024 108 108, g32p_row02_traceSegment_017_3024_0108, g32p_row02_traceSegment_017_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3240 13 14, g32p_row02_traceSegment_017_3240_0013, g32p_row02_traceSegment_017_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3267 13 14, g32p_row02_traceSegment_017_3267_0013, g32p_row02_traceSegment_017_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3240 27 27, g32p_row02_traceSegment_017_3240_0027, g32p_row02_traceSegment_017_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3294 13 14, g32p_row02_traceSegment_017_3294_0013, g32p_row02_traceSegment_017_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3321 13 14, g32p_row02_traceSegment_017_3321_0013, g32p_row02_traceSegment_017_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3294 27 27, g32p_row02_traceSegment_017_3294_0027, g32p_row02_traceSegment_017_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3240 54 54, g32p_row02_traceSegment_017_3240_0054, g32p_row02_traceSegment_017_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3348 13 14, g32p_row02_traceSegment_017_3348_0013, g32p_row02_traceSegment_017_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3375 13 14, g32p_row02_traceSegment_017_3375_0013, g32p_row02_traceSegment_017_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3348 27 27, g32p_row02_traceSegment_017_3348_0027, g32p_row02_traceSegment_017_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3402 13 14, g32p_row02_traceSegment_017_3402_0013, g32p_row02_traceSegment_017_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_017 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_017 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_017_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_017 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3429 13 14, g32p_row02_traceSegment_017_3429_0013, g32p_row02_traceSegment_017_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_017 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3402 27 27, g32p_row02_traceSegment_017_3402_0027, g32p_row02_traceSegment_017_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_017 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3348 54 54, g32p_row02_traceSegment_017_3348_0054, g32p_row02_traceSegment_017_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_017 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3240 108 108, g32p_row02_traceSegment_017_3240_0108, g32p_row02_traceSegment_017_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_017_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_017 3024 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 3024 216 216, g32p_row02_traceSegment_017_3024_0216, g32p_row02_traceSegment_017_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_017_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_017 2592 864 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 2592 432 432, g32p_row02_traceSegment_017_2592_0432, g32p_row02_traceSegment_017_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_017_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_017 1728 1728 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 1728 864 864, g32p_row02_traceSegment_017_1728_0864, g32p_row02_traceSegment_017_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_017_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_017 0 3456 = [0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_017 0 1728 1728, g32p_row02_traceSegment_017_0000_1728, g32p_row02_traceSegment_017_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_017 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 17 = [0, 0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_017_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_018 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 18 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_018_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 0 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 13 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 0 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 0 13 14, g32p_row02_traceSegment_018_0000_0013, g32p_row02_traceSegment_018_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 27 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 27 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 27 13 14, g32p_row02_traceSegment_018_0027_0013, g32p_row02_traceSegment_018_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 0 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 0 27 27, g32p_row02_traceSegment_018_0000_0027, g32p_row02_traceSegment_018_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 54 13 14, g32p_row02_traceSegment_018_0054_0013, g32p_row02_traceSegment_018_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 81 13 14, g32p_row02_traceSegment_018_0081_0013, g32p_row02_traceSegment_018_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 54 27 27, g32p_row02_traceSegment_018_0054_0027, g32p_row02_traceSegment_018_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 0 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 0 54 54, g32p_row02_traceSegment_018_0000_0054, g32p_row02_traceSegment_018_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 121 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 108 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 108 13 14, g32p_row02_traceSegment_018_0108_0013, g32p_row02_traceSegment_018_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 135 13 14, g32p_row02_traceSegment_018_0135_0013, g32p_row02_traceSegment_018_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 108 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 108 27 27, g32p_row02_traceSegment_018_0108_0027, g32p_row02_traceSegment_018_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 162 13 14, g32p_row02_traceSegment_018_0162_0013, g32p_row02_traceSegment_018_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 189 13 14, g32p_row02_traceSegment_018_0189_0013, g32p_row02_traceSegment_018_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 162 27 27, g32p_row02_traceSegment_018_0162_0027, g32p_row02_traceSegment_018_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 108 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 108 54 54, g32p_row02_traceSegment_018_0108_0054, g32p_row02_traceSegment_018_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 0 216 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 0 108 108, g32p_row02_traceSegment_018_0000_0108, g32p_row02_traceSegment_018_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 216 13 14, g32p_row02_traceSegment_018_0216_0013, g32p_row02_traceSegment_018_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 243 13 14, g32p_row02_traceSegment_018_0243_0013, g32p_row02_traceSegment_018_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 216 27 27, g32p_row02_traceSegment_018_0216_0027, g32p_row02_traceSegment_018_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 270 13 14, g32p_row02_traceSegment_018_0270_0013, g32p_row02_traceSegment_018_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 297 13 14, g32p_row02_traceSegment_018_0297_0013, g32p_row02_traceSegment_018_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 270 27 27, g32p_row02_traceSegment_018_0270_0027, g32p_row02_traceSegment_018_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 216 54 54, g32p_row02_traceSegment_018_0216_0054, g32p_row02_traceSegment_018_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 324 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 337 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 324 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 324 13 14, g32p_row02_traceSegment_018_0324_0013, g32p_row02_traceSegment_018_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 351 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 364 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 351 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 351 13 14, g32p_row02_traceSegment_018_0351_0013, g32p_row02_traceSegment_018_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 324 54 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 324 27 27, g32p_row02_traceSegment_018_0324_0027, g32p_row02_traceSegment_018_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 378 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 378 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 378 13 14, g32p_row02_traceSegment_018_0378_0013, g32p_row02_traceSegment_018_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 405 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 405 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 405 13 14, g32p_row02_traceSegment_018_0405_0013, g32p_row02_traceSegment_018_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 378 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 378 27 27, g32p_row02_traceSegment_018_0378_0027, g32p_row02_traceSegment_018_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 324 108 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 324 54 54, g32p_row02_traceSegment_018_0324_0054, g32p_row02_traceSegment_018_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 216 216 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 216 108 108, g32p_row02_traceSegment_018_0216_0108, g32p_row02_traceSegment_018_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_018 0 432 = [0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 0 216 216, g32p_row02_traceSegment_018_0000_0216, g32p_row02_traceSegment_018_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 445 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 432 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 432 13 14, g32p_row02_traceSegment_018_0432_0013, g32p_row02_traceSegment_018_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 459 13 14, g32p_row02_traceSegment_018_0459_0013, g32p_row02_traceSegment_018_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 432 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 432 27 27, g32p_row02_traceSegment_018_0432_0027, g32p_row02_traceSegment_018_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 486 13 14, g32p_row02_traceSegment_018_0486_0013, g32p_row02_traceSegment_018_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 513 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 513 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 513 13 14, g32p_row02_traceSegment_018_0513_0013, g32p_row02_traceSegment_018_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 486 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 486 27 27, g32p_row02_traceSegment_018_0486_0027, g32p_row02_traceSegment_018_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 432 108 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 432 54 54, g32p_row02_traceSegment_018_0432_0054, g32p_row02_traceSegment_018_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 540 13 14, g32p_row02_traceSegment_018_0540_0013, g32p_row02_traceSegment_018_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 567 13 14, g32p_row02_traceSegment_018_0567_0013, g32p_row02_traceSegment_018_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 540 27 27, g32p_row02_traceSegment_018_0540_0027, g32p_row02_traceSegment_018_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 594 13 14, g32p_row02_traceSegment_018_0594_0013, g32p_row02_traceSegment_018_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 621 13 14, g32p_row02_traceSegment_018_0621_0013, g32p_row02_traceSegment_018_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 594 27 27, g32p_row02_traceSegment_018_0594_0027, g32p_row02_traceSegment_018_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 540 54 54, g32p_row02_traceSegment_018_0540_0054, g32p_row02_traceSegment_018_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 432 216 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 432 108 108, g32p_row02_traceSegment_018_0432_0108, g32p_row02_traceSegment_018_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 648 13 14, g32p_row02_traceSegment_018_0648_0013, g32p_row02_traceSegment_018_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 675 13 14, g32p_row02_traceSegment_018_0675_0013, g32p_row02_traceSegment_018_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 648 27 27, g32p_row02_traceSegment_018_0648_0027, g32p_row02_traceSegment_018_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 702 13 14, g32p_row02_traceSegment_018_0702_0013, g32p_row02_traceSegment_018_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 729 13 14, g32p_row02_traceSegment_018_0729_0013, g32p_row02_traceSegment_018_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 702 27 27, g32p_row02_traceSegment_018_0702_0027, g32p_row02_traceSegment_018_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 648 54 54, g32p_row02_traceSegment_018_0648_0054, g32p_row02_traceSegment_018_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 756 13 14, g32p_row02_traceSegment_018_0756_0013, g32p_row02_traceSegment_018_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 783 13 14, g32p_row02_traceSegment_018_0783_0013, g32p_row02_traceSegment_018_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 756 27 27, g32p_row02_traceSegment_018_0756_0027, g32p_row02_traceSegment_018_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 810 13 14, g32p_row02_traceSegment_018_0810_0013, g32p_row02_traceSegment_018_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 837 13 14, g32p_row02_traceSegment_018_0837_0013, g32p_row02_traceSegment_018_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 810 27 27, g32p_row02_traceSegment_018_0810_0027, g32p_row02_traceSegment_018_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 756 54 54, g32p_row02_traceSegment_018_0756_0054, g32p_row02_traceSegment_018_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 648 108 108, g32p_row02_traceSegment_018_0648_0108, g32p_row02_traceSegment_018_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_018 432 432 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 432 216 216, g32p_row02_traceSegment_018_0432_0216, g32p_row02_traceSegment_018_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_018 0 864 = [1, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 0 432 432, g32p_row02_traceSegment_018_0000_0432, g32p_row02_traceSegment_018_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 864 13 14, g32p_row02_traceSegment_018_0864_0013, g32p_row02_traceSegment_018_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 891 13 14, g32p_row02_traceSegment_018_0891_0013, g32p_row02_traceSegment_018_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 864 27 27, g32p_row02_traceSegment_018_0864_0027, g32p_row02_traceSegment_018_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 918 13 14, g32p_row02_traceSegment_018_0918_0013, g32p_row02_traceSegment_018_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 945 13 14, g32p_row02_traceSegment_018_0945_0013, g32p_row02_traceSegment_018_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 918 27 27, g32p_row02_traceSegment_018_0918_0027, g32p_row02_traceSegment_018_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 864 54 54, g32p_row02_traceSegment_018_0864_0054, g32p_row02_traceSegment_018_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 972 13 14, g32p_row02_traceSegment_018_0972_0013, g32p_row02_traceSegment_018_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 999 13 14, g32p_row02_traceSegment_018_0999_0013, g32p_row02_traceSegment_018_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 972 27 27, g32p_row02_traceSegment_018_0972_0027, g32p_row02_traceSegment_018_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1026 13 14, g32p_row02_traceSegment_018_1026_0013, g32p_row02_traceSegment_018_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1053 13 14, g32p_row02_traceSegment_018_1053_0013, g32p_row02_traceSegment_018_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1026 27 27, g32p_row02_traceSegment_018_1026_0027, g32p_row02_traceSegment_018_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 972 54 54, g32p_row02_traceSegment_018_0972_0054, g32p_row02_traceSegment_018_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 864 108 108, g32p_row02_traceSegment_018_0864_0108, g32p_row02_traceSegment_018_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1080 13 14, g32p_row02_traceSegment_018_1080_0013, g32p_row02_traceSegment_018_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1107 13 14, g32p_row02_traceSegment_018_1107_0013, g32p_row02_traceSegment_018_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1080 27 27, g32p_row02_traceSegment_018_1080_0027, g32p_row02_traceSegment_018_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1134 13 14, g32p_row02_traceSegment_018_1134_0013, g32p_row02_traceSegment_018_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1161 13 14, g32p_row02_traceSegment_018_1161_0013, g32p_row02_traceSegment_018_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1134 27 27, g32p_row02_traceSegment_018_1134_0027, g32p_row02_traceSegment_018_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1080 54 54, g32p_row02_traceSegment_018_1080_0054, g32p_row02_traceSegment_018_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1188 13 14, g32p_row02_traceSegment_018_1188_0013, g32p_row02_traceSegment_018_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1215 13 14, g32p_row02_traceSegment_018_1215_0013, g32p_row02_traceSegment_018_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1188 27 27, g32p_row02_traceSegment_018_1188_0027, g32p_row02_traceSegment_018_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1242 13 14, g32p_row02_traceSegment_018_1242_0013, g32p_row02_traceSegment_018_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1269 13 14, g32p_row02_traceSegment_018_1269_0013, g32p_row02_traceSegment_018_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1242 27 27, g32p_row02_traceSegment_018_1242_0027, g32p_row02_traceSegment_018_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1188 54 54, g32p_row02_traceSegment_018_1188_0054, g32p_row02_traceSegment_018_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1080 108 108, g32p_row02_traceSegment_018_1080_0108, g32p_row02_traceSegment_018_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_018 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 864 216 216, g32p_row02_traceSegment_018_0864_0216, g32p_row02_traceSegment_018_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1296 13 14, g32p_row02_traceSegment_018_1296_0013, g32p_row02_traceSegment_018_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1323 13 14, g32p_row02_traceSegment_018_1323_0013, g32p_row02_traceSegment_018_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1296 27 27, g32p_row02_traceSegment_018_1296_0027, g32p_row02_traceSegment_018_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1350 13 14, g32p_row02_traceSegment_018_1350_0013, g32p_row02_traceSegment_018_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1377 13 14, g32p_row02_traceSegment_018_1377_0013, g32p_row02_traceSegment_018_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1350 27 27, g32p_row02_traceSegment_018_1350_0027, g32p_row02_traceSegment_018_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1296 54 54, g32p_row02_traceSegment_018_1296_0054, g32p_row02_traceSegment_018_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1404 13 14, g32p_row02_traceSegment_018_1404_0013, g32p_row02_traceSegment_018_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1431 13 14, g32p_row02_traceSegment_018_1431_0013, g32p_row02_traceSegment_018_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1404 27 27, g32p_row02_traceSegment_018_1404_0027, g32p_row02_traceSegment_018_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1458 13 14, g32p_row02_traceSegment_018_1458_0013, g32p_row02_traceSegment_018_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1485 13 14, g32p_row02_traceSegment_018_1485_0013, g32p_row02_traceSegment_018_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1458 27 27, g32p_row02_traceSegment_018_1458_0027, g32p_row02_traceSegment_018_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1404 54 54, g32p_row02_traceSegment_018_1404_0054, g32p_row02_traceSegment_018_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1296 108 108, g32p_row02_traceSegment_018_1296_0108, g32p_row02_traceSegment_018_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1512 13 14, g32p_row02_traceSegment_018_1512_0013, g32p_row02_traceSegment_018_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1552 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1539 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1539 13 14, g32p_row02_traceSegment_018_1539_0013, g32p_row02_traceSegment_018_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1512 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1512 27 27, g32p_row02_traceSegment_018_1512_0027, g32p_row02_traceSegment_018_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1566 13 14, g32p_row02_traceSegment_018_1566_0013, g32p_row02_traceSegment_018_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1593 13 14, g32p_row02_traceSegment_018_1593_0013, g32p_row02_traceSegment_018_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1566 27 27, g32p_row02_traceSegment_018_1566_0027, g32p_row02_traceSegment_018_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 1512 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1512 54 54, g32p_row02_traceSegment_018_1512_0054, g32p_row02_traceSegment_018_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1620 13 14, g32p_row02_traceSegment_018_1620_0013, g32p_row02_traceSegment_018_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1647 13 14, g32p_row02_traceSegment_018_1647_0013, g32p_row02_traceSegment_018_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1620 27 27, g32p_row02_traceSegment_018_1620_0027, g32p_row02_traceSegment_018_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1674 13 14, g32p_row02_traceSegment_018_1674_0013, g32p_row02_traceSegment_018_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1701 13 14, g32p_row02_traceSegment_018_1701_0013, g32p_row02_traceSegment_018_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1674 27 27, g32p_row02_traceSegment_018_1674_0027, g32p_row02_traceSegment_018_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1620 54 54, g32p_row02_traceSegment_018_1620_0054, g32p_row02_traceSegment_018_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 1512 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1512 108 108, g32p_row02_traceSegment_018_1512_0108, g32p_row02_traceSegment_018_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_018 1296 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1296 216 216, g32p_row02_traceSegment_018_1296_0216, g32p_row02_traceSegment_018_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_018 864 864 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 864 432 432, g32p_row02_traceSegment_018_0864_0432, g32p_row02_traceSegment_018_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_018 0 1728 = [2, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 0 864 864, g32p_row02_traceSegment_018_0000_0864, g32p_row02_traceSegment_018_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1728 13 14, g32p_row02_traceSegment_018_1728_0013, g32p_row02_traceSegment_018_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1755 13 14, g32p_row02_traceSegment_018_1755_0013, g32p_row02_traceSegment_018_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1728 27 27, g32p_row02_traceSegment_018_1728_0027, g32p_row02_traceSegment_018_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1782 13 14, g32p_row02_traceSegment_018_1782_0013, g32p_row02_traceSegment_018_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1809 13 14, g32p_row02_traceSegment_018_1809_0013, g32p_row02_traceSegment_018_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1782 27 27, g32p_row02_traceSegment_018_1782_0027, g32p_row02_traceSegment_018_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1728 54 54, g32p_row02_traceSegment_018_1728_0054, g32p_row02_traceSegment_018_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1836 13 14, g32p_row02_traceSegment_018_1836_0013, g32p_row02_traceSegment_018_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1863 13 14, g32p_row02_traceSegment_018_1863_0013, g32p_row02_traceSegment_018_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1836 27 27, g32p_row02_traceSegment_018_1836_0027, g32p_row02_traceSegment_018_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1890 13 14, g32p_row02_traceSegment_018_1890_0013, g32p_row02_traceSegment_018_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1917 13 14, g32p_row02_traceSegment_018_1917_0013, g32p_row02_traceSegment_018_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1890 27 27, g32p_row02_traceSegment_018_1890_0027, g32p_row02_traceSegment_018_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1836 54 54, g32p_row02_traceSegment_018_1836_0054, g32p_row02_traceSegment_018_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1728 108 108, g32p_row02_traceSegment_018_1728_0108, g32p_row02_traceSegment_018_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1944 13 14, g32p_row02_traceSegment_018_1944_0013, g32p_row02_traceSegment_018_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1971 13 14, g32p_row02_traceSegment_018_1971_0013, g32p_row02_traceSegment_018_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1944 27 27, g32p_row02_traceSegment_018_1944_0027, g32p_row02_traceSegment_018_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1998 13 14, g32p_row02_traceSegment_018_1998_0013, g32p_row02_traceSegment_018_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2025 13 14, g32p_row02_traceSegment_018_2025_0013, g32p_row02_traceSegment_018_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1998 27 27, g32p_row02_traceSegment_018_1998_0027, g32p_row02_traceSegment_018_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1944 54 54, g32p_row02_traceSegment_018_1944_0054, g32p_row02_traceSegment_018_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2052 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2052 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2052 13 14, g32p_row02_traceSegment_018_2052_0013, g32p_row02_traceSegment_018_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2079 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2092 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2079 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2079 13 14, g32p_row02_traceSegment_018_2079_0013, g32p_row02_traceSegment_018_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2052 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2052 27 27, g32p_row02_traceSegment_018_2052_0027, g32p_row02_traceSegment_018_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2106 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2106 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2106 13 14, g32p_row02_traceSegment_018_2106_0013, g32p_row02_traceSegment_018_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2133 13 14, g32p_row02_traceSegment_018_2133_0013, g32p_row02_traceSegment_018_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2106 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2106 27 27, g32p_row02_traceSegment_018_2106_0027, g32p_row02_traceSegment_018_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 2052 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2052 54 54, g32p_row02_traceSegment_018_2052_0054, g32p_row02_traceSegment_018_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 1944 216 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1944 108 108, g32p_row02_traceSegment_018_1944_0108, g32p_row02_traceSegment_018_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_018 1728 432 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1728 216 216, g32p_row02_traceSegment_018_1728_0216, g32p_row02_traceSegment_018_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2160 13 14, g32p_row02_traceSegment_018_2160_0013, g32p_row02_traceSegment_018_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2187 13 14, g32p_row02_traceSegment_018_2187_0013, g32p_row02_traceSegment_018_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2160 27 27, g32p_row02_traceSegment_018_2160_0027, g32p_row02_traceSegment_018_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2214 13 14, g32p_row02_traceSegment_018_2214_0013, g32p_row02_traceSegment_018_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2241 13 14, g32p_row02_traceSegment_018_2241_0013, g32p_row02_traceSegment_018_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2214 27 27, g32p_row02_traceSegment_018_2214_0027, g32p_row02_traceSegment_018_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2160 54 54, g32p_row02_traceSegment_018_2160_0054, g32p_row02_traceSegment_018_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2281 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2268 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2268 13 14, g32p_row02_traceSegment_018_2268_0013, g32p_row02_traceSegment_018_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2295 13 14, g32p_row02_traceSegment_018_2295_0013, g32p_row02_traceSegment_018_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2268 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2268 27 27, g32p_row02_traceSegment_018_2268_0027, g32p_row02_traceSegment_018_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2335 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2322 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2322 13 14, g32p_row02_traceSegment_018_2322_0013, g32p_row02_traceSegment_018_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2349 13 14, g32p_row02_traceSegment_018_2349_0013, g32p_row02_traceSegment_018_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2322 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2322 27 27, g32p_row02_traceSegment_018_2322_0027, g32p_row02_traceSegment_018_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 2268 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2268 54 54, g32p_row02_traceSegment_018_2268_0054, g32p_row02_traceSegment_018_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 2160 216 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2160 108 108, g32p_row02_traceSegment_018_2160_0108, g32p_row02_traceSegment_018_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2376 13 14, g32p_row02_traceSegment_018_2376_0013, g32p_row02_traceSegment_018_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2403 13 14, g32p_row02_traceSegment_018_2403_0013, g32p_row02_traceSegment_018_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2376 27 27, g32p_row02_traceSegment_018_2376_0027, g32p_row02_traceSegment_018_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2430 13 14, g32p_row02_traceSegment_018_2430_0013, g32p_row02_traceSegment_018_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2457 13 14, g32p_row02_traceSegment_018_2457_0013, g32p_row02_traceSegment_018_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2430 27 27, g32p_row02_traceSegment_018_2430_0027, g32p_row02_traceSegment_018_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2376 54 54, g32p_row02_traceSegment_018_2376_0054, g32p_row02_traceSegment_018_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2484 13 14, g32p_row02_traceSegment_018_2484_0013, g32p_row02_traceSegment_018_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2511 13 14, g32p_row02_traceSegment_018_2511_0013, g32p_row02_traceSegment_018_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2484 27 27, g32p_row02_traceSegment_018_2484_0027, g32p_row02_traceSegment_018_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2538 13 14, g32p_row02_traceSegment_018_2538_0013, g32p_row02_traceSegment_018_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2565 13 14, g32p_row02_traceSegment_018_2565_0013, g32p_row02_traceSegment_018_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2538 27 27, g32p_row02_traceSegment_018_2538_0027, g32p_row02_traceSegment_018_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2484 54 54, g32p_row02_traceSegment_018_2484_0054, g32p_row02_traceSegment_018_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2376 108 108, g32p_row02_traceSegment_018_2376_0108, g32p_row02_traceSegment_018_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_018 2160 432 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2160 216 216, g32p_row02_traceSegment_018_2160_0216, g32p_row02_traceSegment_018_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_018 1728 864 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1728 432 432, g32p_row02_traceSegment_018_1728_0432, g32p_row02_traceSegment_018_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2592 13 14, g32p_row02_traceSegment_018_2592_0013, g32p_row02_traceSegment_018_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2619 13 14, g32p_row02_traceSegment_018_2619_0013, g32p_row02_traceSegment_018_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2592 27 27, g32p_row02_traceSegment_018_2592_0027, g32p_row02_traceSegment_018_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2646 13 14, g32p_row02_traceSegment_018_2646_0013, g32p_row02_traceSegment_018_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2673 13 14, g32p_row02_traceSegment_018_2673_0013, g32p_row02_traceSegment_018_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2646 27 27, g32p_row02_traceSegment_018_2646_0027, g32p_row02_traceSegment_018_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2592 54 54, g32p_row02_traceSegment_018_2592_0054, g32p_row02_traceSegment_018_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2700 13 14, g32p_row02_traceSegment_018_2700_0013, g32p_row02_traceSegment_018_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2727 13 14, g32p_row02_traceSegment_018_2727_0013, g32p_row02_traceSegment_018_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2700 27 27, g32p_row02_traceSegment_018_2700_0027, g32p_row02_traceSegment_018_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2754 13 14, g32p_row02_traceSegment_018_2754_0013, g32p_row02_traceSegment_018_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2781 13 14, g32p_row02_traceSegment_018_2781_0013, g32p_row02_traceSegment_018_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2754 27 27, g32p_row02_traceSegment_018_2754_0027, g32p_row02_traceSegment_018_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2700 54 54, g32p_row02_traceSegment_018_2700_0054, g32p_row02_traceSegment_018_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2592 108 108, g32p_row02_traceSegment_018_2592_0108, g32p_row02_traceSegment_018_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2808 13 14, g32p_row02_traceSegment_018_2808_0013, g32p_row02_traceSegment_018_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2835 13 14, g32p_row02_traceSegment_018_2835_0013, g32p_row02_traceSegment_018_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2808 27 27, g32p_row02_traceSegment_018_2808_0027, g32p_row02_traceSegment_018_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2862 13 14, g32p_row02_traceSegment_018_2862_0013, g32p_row02_traceSegment_018_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2889 13 14, g32p_row02_traceSegment_018_2889_0013, g32p_row02_traceSegment_018_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2862 27 27, g32p_row02_traceSegment_018_2862_0027, g32p_row02_traceSegment_018_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2808 54 54, g32p_row02_traceSegment_018_2808_0054, g32p_row02_traceSegment_018_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2916 13 14, g32p_row02_traceSegment_018_2916_0013, g32p_row02_traceSegment_018_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2943 13 14, g32p_row02_traceSegment_018_2943_0013, g32p_row02_traceSegment_018_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2916 27 27, g32p_row02_traceSegment_018_2916_0027, g32p_row02_traceSegment_018_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2970 13 14, g32p_row02_traceSegment_018_2970_0013, g32p_row02_traceSegment_018_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2997 13 14, g32p_row02_traceSegment_018_2997_0013, g32p_row02_traceSegment_018_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2970 27 27, g32p_row02_traceSegment_018_2970_0027, g32p_row02_traceSegment_018_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2916 54 54, g32p_row02_traceSegment_018_2916_0054, g32p_row02_traceSegment_018_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2808 108 108, g32p_row02_traceSegment_018_2808_0108, g32p_row02_traceSegment_018_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_018 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2592 216 216, g32p_row02_traceSegment_018_2592_0216, g32p_row02_traceSegment_018_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3024 13 14, g32p_row02_traceSegment_018_3024_0013, g32p_row02_traceSegment_018_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3051 13 14, g32p_row02_traceSegment_018_3051_0013, g32p_row02_traceSegment_018_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3024 27 27, g32p_row02_traceSegment_018_3024_0027, g32p_row02_traceSegment_018_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3078 13 14, g32p_row02_traceSegment_018_3078_0013, g32p_row02_traceSegment_018_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3105 13 14, g32p_row02_traceSegment_018_3105_0013, g32p_row02_traceSegment_018_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3078 27 27, g32p_row02_traceSegment_018_3078_0027, g32p_row02_traceSegment_018_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3024 54 54, g32p_row02_traceSegment_018_3024_0054, g32p_row02_traceSegment_018_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3132 13 14, g32p_row02_traceSegment_018_3132_0013, g32p_row02_traceSegment_018_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3159 13 14, g32p_row02_traceSegment_018_3159_0013, g32p_row02_traceSegment_018_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3132 27 27, g32p_row02_traceSegment_018_3132_0027, g32p_row02_traceSegment_018_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3186 13 14, g32p_row02_traceSegment_018_3186_0013, g32p_row02_traceSegment_018_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3213 13 14, g32p_row02_traceSegment_018_3213_0013, g32p_row02_traceSegment_018_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3186 27 27, g32p_row02_traceSegment_018_3186_0027, g32p_row02_traceSegment_018_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3132 54 54, g32p_row02_traceSegment_018_3132_0054, g32p_row02_traceSegment_018_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3024 108 108, g32p_row02_traceSegment_018_3024_0108, g32p_row02_traceSegment_018_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3240 13 14, g32p_row02_traceSegment_018_3240_0013, g32p_row02_traceSegment_018_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3267 13 14, g32p_row02_traceSegment_018_3267_0013, g32p_row02_traceSegment_018_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3240 27 27, g32p_row02_traceSegment_018_3240_0027, g32p_row02_traceSegment_018_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3294 13 14, g32p_row02_traceSegment_018_3294_0013, g32p_row02_traceSegment_018_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3321 13 14, g32p_row02_traceSegment_018_3321_0013, g32p_row02_traceSegment_018_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3294 27 27, g32p_row02_traceSegment_018_3294_0027, g32p_row02_traceSegment_018_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3240 54 54, g32p_row02_traceSegment_018_3240_0054, g32p_row02_traceSegment_018_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3348 13 14, g32p_row02_traceSegment_018_3348_0013, g32p_row02_traceSegment_018_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3375 13 14, g32p_row02_traceSegment_018_3375_0013, g32p_row02_traceSegment_018_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3348 27 27, g32p_row02_traceSegment_018_3348_0027, g32p_row02_traceSegment_018_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3402 13 14, g32p_row02_traceSegment_018_3402_0013, g32p_row02_traceSegment_018_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_018 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_018 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_018_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_018 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3429 13 14, g32p_row02_traceSegment_018_3429_0013, g32p_row02_traceSegment_018_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_018 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3402 27 27, g32p_row02_traceSegment_018_3402_0027, g32p_row02_traceSegment_018_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_018 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3348 54 54, g32p_row02_traceSegment_018_3348_0054, g32p_row02_traceSegment_018_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_018 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3240 108 108, g32p_row02_traceSegment_018_3240_0108, g32p_row02_traceSegment_018_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_018_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_018 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 3024 216 216, g32p_row02_traceSegment_018_3024_0216, g32p_row02_traceSegment_018_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_018_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_018 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 2592 432 432, g32p_row02_traceSegment_018_2592_0432, g32p_row02_traceSegment_018_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_018_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_018 1728 1728 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 1728 864 864, g32p_row02_traceSegment_018_1728_0864, g32p_row02_traceSegment_018_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_018_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_018 0 3456 = [2, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_018 0 1728 1728, g32p_row02_traceSegment_018_0000_1728, g32p_row02_traceSegment_018_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 18 = [2, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_018_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_019 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 19 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_019_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 0 13 14, g32p_row02_traceSegment_019_0000_0013, g32p_row02_traceSegment_019_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 27 13 14, g32p_row02_traceSegment_019_0027_0013, g32p_row02_traceSegment_019_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 0 27 27, g32p_row02_traceSegment_019_0000_0027, g32p_row02_traceSegment_019_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 54 13 14, g32p_row02_traceSegment_019_0054_0013, g32p_row02_traceSegment_019_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 81 13 14, g32p_row02_traceSegment_019_0081_0013, g32p_row02_traceSegment_019_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 54 27 27, g32p_row02_traceSegment_019_0054_0027, g32p_row02_traceSegment_019_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 0 54 54, g32p_row02_traceSegment_019_0000_0054, g32p_row02_traceSegment_019_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 108 13 14, g32p_row02_traceSegment_019_0108_0013, g32p_row02_traceSegment_019_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 135 13 14, g32p_row02_traceSegment_019_0135_0013, g32p_row02_traceSegment_019_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 108 27 27, g32p_row02_traceSegment_019_0108_0027, g32p_row02_traceSegment_019_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 162 13 14, g32p_row02_traceSegment_019_0162_0013, g32p_row02_traceSegment_019_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 189 13 14, g32p_row02_traceSegment_019_0189_0013, g32p_row02_traceSegment_019_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 162 27 27, g32p_row02_traceSegment_019_0162_0027, g32p_row02_traceSegment_019_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 108 54 54, g32p_row02_traceSegment_019_0108_0054, g32p_row02_traceSegment_019_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 0 108 108, g32p_row02_traceSegment_019_0000_0108, g32p_row02_traceSegment_019_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 216 13 14, g32p_row02_traceSegment_019_0216_0013, g32p_row02_traceSegment_019_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 243 13 14, g32p_row02_traceSegment_019_0243_0013, g32p_row02_traceSegment_019_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 216 27 27, g32p_row02_traceSegment_019_0216_0027, g32p_row02_traceSegment_019_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 270 13 14, g32p_row02_traceSegment_019_0270_0013, g32p_row02_traceSegment_019_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 297 13 14, g32p_row02_traceSegment_019_0297_0013, g32p_row02_traceSegment_019_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 270 27 27, g32p_row02_traceSegment_019_0270_0027, g32p_row02_traceSegment_019_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 216 54 54, g32p_row02_traceSegment_019_0216_0054, g32p_row02_traceSegment_019_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 324 13 14, g32p_row02_traceSegment_019_0324_0013, g32p_row02_traceSegment_019_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 351 13 14, g32p_row02_traceSegment_019_0351_0013, g32p_row02_traceSegment_019_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 324 27 27, g32p_row02_traceSegment_019_0324_0027, g32p_row02_traceSegment_019_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 378 13 14, g32p_row02_traceSegment_019_0378_0013, g32p_row02_traceSegment_019_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 405 13 14, g32p_row02_traceSegment_019_0405_0013, g32p_row02_traceSegment_019_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 378 27 27, g32p_row02_traceSegment_019_0378_0027, g32p_row02_traceSegment_019_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 324 54 54, g32p_row02_traceSegment_019_0324_0054, g32p_row02_traceSegment_019_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 216 108 108, g32p_row02_traceSegment_019_0216_0108, g32p_row02_traceSegment_019_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_019 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 0 216 216, g32p_row02_traceSegment_019_0000_0216, g32p_row02_traceSegment_019_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 432 13 14, g32p_row02_traceSegment_019_0432_0013, g32p_row02_traceSegment_019_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 459 13 14, g32p_row02_traceSegment_019_0459_0013, g32p_row02_traceSegment_019_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 432 27 27, g32p_row02_traceSegment_019_0432_0027, g32p_row02_traceSegment_019_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 486 13 14, g32p_row02_traceSegment_019_0486_0013, g32p_row02_traceSegment_019_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 513 13 14, g32p_row02_traceSegment_019_0513_0013, g32p_row02_traceSegment_019_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 486 27 27, g32p_row02_traceSegment_019_0486_0027, g32p_row02_traceSegment_019_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 432 54 54, g32p_row02_traceSegment_019_0432_0054, g32p_row02_traceSegment_019_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 553 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 540 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 540 13 14, g32p_row02_traceSegment_019_0540_0013, g32p_row02_traceSegment_019_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 567 13 14, g32p_row02_traceSegment_019_0567_0013, g32p_row02_traceSegment_019_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 540 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 540 27 27, g32p_row02_traceSegment_019_0540_0027, g32p_row02_traceSegment_019_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 594 13 14, g32p_row02_traceSegment_019_0594_0013, g32p_row02_traceSegment_019_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 621 13 14, g32p_row02_traceSegment_019_0621_0013, g32p_row02_traceSegment_019_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 594 27 27, g32p_row02_traceSegment_019_0594_0027, g32p_row02_traceSegment_019_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 540 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 540 54 54, g32p_row02_traceSegment_019_0540_0054, g32p_row02_traceSegment_019_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 432 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 432 108 108, g32p_row02_traceSegment_019_0432_0108, g32p_row02_traceSegment_019_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 648 13 14, g32p_row02_traceSegment_019_0648_0013, g32p_row02_traceSegment_019_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 675 13 14, g32p_row02_traceSegment_019_0675_0013, g32p_row02_traceSegment_019_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 648 27 27, g32p_row02_traceSegment_019_0648_0027, g32p_row02_traceSegment_019_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 702 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 702 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 702 13 14, g32p_row02_traceSegment_019_0702_0013, g32p_row02_traceSegment_019_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 729 13 14, g32p_row02_traceSegment_019_0729_0013, g32p_row02_traceSegment_019_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 702 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 702 27 27, g32p_row02_traceSegment_019_0702_0027, g32p_row02_traceSegment_019_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 648 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 648 54 54, g32p_row02_traceSegment_019_0648_0054, g32p_row02_traceSegment_019_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 756 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 756 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 756 13 14, g32p_row02_traceSegment_019_0756_0013, g32p_row02_traceSegment_019_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 783 13 14, g32p_row02_traceSegment_019_0783_0013, g32p_row02_traceSegment_019_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 756 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 756 27 27, g32p_row02_traceSegment_019_0756_0027, g32p_row02_traceSegment_019_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 810 13 14, g32p_row02_traceSegment_019_0810_0013, g32p_row02_traceSegment_019_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 837 13 14, g32p_row02_traceSegment_019_0837_0013, g32p_row02_traceSegment_019_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 810 27 27, g32p_row02_traceSegment_019_0810_0027, g32p_row02_traceSegment_019_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 756 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 756 54 54, g32p_row02_traceSegment_019_0756_0054, g32p_row02_traceSegment_019_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 648 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 648 108 108, g32p_row02_traceSegment_019_0648_0108, g32p_row02_traceSegment_019_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_019 432 432 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 432 216 216, g32p_row02_traceSegment_019_0432_0216, g32p_row02_traceSegment_019_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_019 0 864 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 0 432 432, g32p_row02_traceSegment_019_0000_0432, g32p_row02_traceSegment_019_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 864 13 14, g32p_row02_traceSegment_019_0864_0013, g32p_row02_traceSegment_019_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 891 13 14, g32p_row02_traceSegment_019_0891_0013, g32p_row02_traceSegment_019_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 864 27 27, g32p_row02_traceSegment_019_0864_0027, g32p_row02_traceSegment_019_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 918 13 14, g32p_row02_traceSegment_019_0918_0013, g32p_row02_traceSegment_019_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 945 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 958 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 945 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 945 13 14, g32p_row02_traceSegment_019_0945_0013, g32p_row02_traceSegment_019_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 918 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 918 27 27, g32p_row02_traceSegment_019_0918_0027, g32p_row02_traceSegment_019_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 864 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 864 54 54, g32p_row02_traceSegment_019_0864_0054, g32p_row02_traceSegment_019_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 985 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 972 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 972 13 14, g32p_row02_traceSegment_019_0972_0013, g32p_row02_traceSegment_019_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 999 13 14, g32p_row02_traceSegment_019_0999_0013, g32p_row02_traceSegment_019_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 972 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 972 27 27, g32p_row02_traceSegment_019_0972_0027, g32p_row02_traceSegment_019_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1026 13 14, g32p_row02_traceSegment_019_1026_0013, g32p_row02_traceSegment_019_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1053 13 14, g32p_row02_traceSegment_019_1053_0013, g32p_row02_traceSegment_019_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1026 27 27, g32p_row02_traceSegment_019_1026_0027, g32p_row02_traceSegment_019_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 972 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 972 54 54, g32p_row02_traceSegment_019_0972_0054, g32p_row02_traceSegment_019_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 864 216 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 864 108 108, g32p_row02_traceSegment_019_0864_0108, g32p_row02_traceSegment_019_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1080 13 14, g32p_row02_traceSegment_019_1080_0013, g32p_row02_traceSegment_019_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1107 13 14, g32p_row02_traceSegment_019_1107_0013, g32p_row02_traceSegment_019_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1080 27 27, g32p_row02_traceSegment_019_1080_0027, g32p_row02_traceSegment_019_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1134 13 14, g32p_row02_traceSegment_019_1134_0013, g32p_row02_traceSegment_019_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1161 13 14, g32p_row02_traceSegment_019_1161_0013, g32p_row02_traceSegment_019_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1134 27 27, g32p_row02_traceSegment_019_1134_0027, g32p_row02_traceSegment_019_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1080 54 54, g32p_row02_traceSegment_019_1080_0054, g32p_row02_traceSegment_019_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1188 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1188 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1188 13 14, g32p_row02_traceSegment_019_1188_0013, g32p_row02_traceSegment_019_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1215 13 14, g32p_row02_traceSegment_019_1215_0013, g32p_row02_traceSegment_019_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1188 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1188 27 27, g32p_row02_traceSegment_019_1188_0027, g32p_row02_traceSegment_019_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1242 13 14, g32p_row02_traceSegment_019_1242_0013, g32p_row02_traceSegment_019_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1269 13 14, g32p_row02_traceSegment_019_1269_0013, g32p_row02_traceSegment_019_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1242 27 27, g32p_row02_traceSegment_019_1242_0027, g32p_row02_traceSegment_019_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 1188 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1188 54 54, g32p_row02_traceSegment_019_1188_0054, g32p_row02_traceSegment_019_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 1080 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1080 108 108, g32p_row02_traceSegment_019_1080_0108, g32p_row02_traceSegment_019_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_019 864 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 864 216 216, g32p_row02_traceSegment_019_0864_0216, g32p_row02_traceSegment_019_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1296 13 14, g32p_row02_traceSegment_019_1296_0013, g32p_row02_traceSegment_019_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1323 13 14, g32p_row02_traceSegment_019_1323_0013, g32p_row02_traceSegment_019_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1296 27 27, g32p_row02_traceSegment_019_1296_0027, g32p_row02_traceSegment_019_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1350 13 14, g32p_row02_traceSegment_019_1350_0013, g32p_row02_traceSegment_019_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1377 13 14, g32p_row02_traceSegment_019_1377_0013, g32p_row02_traceSegment_019_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1350 27 27, g32p_row02_traceSegment_019_1350_0027, g32p_row02_traceSegment_019_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1296 54 54, g32p_row02_traceSegment_019_1296_0054, g32p_row02_traceSegment_019_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1404 13 14, g32p_row02_traceSegment_019_1404_0013, g32p_row02_traceSegment_019_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1431 13 14, g32p_row02_traceSegment_019_1431_0013, g32p_row02_traceSegment_019_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1404 27 27, g32p_row02_traceSegment_019_1404_0027, g32p_row02_traceSegment_019_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1458 13 14, g32p_row02_traceSegment_019_1458_0013, g32p_row02_traceSegment_019_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1485 13 14, g32p_row02_traceSegment_019_1485_0013, g32p_row02_traceSegment_019_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1458 27 27, g32p_row02_traceSegment_019_1458_0027, g32p_row02_traceSegment_019_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1404 54 54, g32p_row02_traceSegment_019_1404_0054, g32p_row02_traceSegment_019_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1296 108 108, g32p_row02_traceSegment_019_1296_0108, g32p_row02_traceSegment_019_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1512 13 14, g32p_row02_traceSegment_019_1512_0013, g32p_row02_traceSegment_019_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1539 13 14, g32p_row02_traceSegment_019_1539_0013, g32p_row02_traceSegment_019_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1512 27 27, g32p_row02_traceSegment_019_1512_0027, g32p_row02_traceSegment_019_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1566 13 14, g32p_row02_traceSegment_019_1566_0013, g32p_row02_traceSegment_019_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1593 13 14, g32p_row02_traceSegment_019_1593_0013, g32p_row02_traceSegment_019_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1566 27 27, g32p_row02_traceSegment_019_1566_0027, g32p_row02_traceSegment_019_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1512 54 54, g32p_row02_traceSegment_019_1512_0054, g32p_row02_traceSegment_019_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1620 13 14, g32p_row02_traceSegment_019_1620_0013, g32p_row02_traceSegment_019_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1647 13 14, g32p_row02_traceSegment_019_1647_0013, g32p_row02_traceSegment_019_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1620 27 27, g32p_row02_traceSegment_019_1620_0027, g32p_row02_traceSegment_019_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1674 13 14, g32p_row02_traceSegment_019_1674_0013, g32p_row02_traceSegment_019_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1701 13 14, g32p_row02_traceSegment_019_1701_0013, g32p_row02_traceSegment_019_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1674 27 27, g32p_row02_traceSegment_019_1674_0027, g32p_row02_traceSegment_019_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1620 54 54, g32p_row02_traceSegment_019_1620_0054, g32p_row02_traceSegment_019_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1512 108 108, g32p_row02_traceSegment_019_1512_0108, g32p_row02_traceSegment_019_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_019 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1296 216 216, g32p_row02_traceSegment_019_1296_0216, g32p_row02_traceSegment_019_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_019 864 864 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 864 432 432, g32p_row02_traceSegment_019_0864_0432, g32p_row02_traceSegment_019_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_019 0 1728 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 0 864 864, g32p_row02_traceSegment_019_0000_0864, g32p_row02_traceSegment_019_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1728 13 14, g32p_row02_traceSegment_019_1728_0013, g32p_row02_traceSegment_019_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1755 13 14, g32p_row02_traceSegment_019_1755_0013, g32p_row02_traceSegment_019_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1728 27 27, g32p_row02_traceSegment_019_1728_0027, g32p_row02_traceSegment_019_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1782 13 14, g32p_row02_traceSegment_019_1782_0013, g32p_row02_traceSegment_019_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1809 13 14, g32p_row02_traceSegment_019_1809_0013, g32p_row02_traceSegment_019_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1782 27 27, g32p_row02_traceSegment_019_1782_0027, g32p_row02_traceSegment_019_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1728 54 54, g32p_row02_traceSegment_019_1728_0054, g32p_row02_traceSegment_019_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1836 13 14, g32p_row02_traceSegment_019_1836_0013, g32p_row02_traceSegment_019_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1863 13 14, g32p_row02_traceSegment_019_1863_0013, g32p_row02_traceSegment_019_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1836 27 27, g32p_row02_traceSegment_019_1836_0027, g32p_row02_traceSegment_019_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1890 13 14, g32p_row02_traceSegment_019_1890_0013, g32p_row02_traceSegment_019_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1917 13 14, g32p_row02_traceSegment_019_1917_0013, g32p_row02_traceSegment_019_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1890 27 27, g32p_row02_traceSegment_019_1890_0027, g32p_row02_traceSegment_019_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1836 54 54, g32p_row02_traceSegment_019_1836_0054, g32p_row02_traceSegment_019_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1728 108 108, g32p_row02_traceSegment_019_1728_0108, g32p_row02_traceSegment_019_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1944 13 14, g32p_row02_traceSegment_019_1944_0013, g32p_row02_traceSegment_019_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1971 13 14, g32p_row02_traceSegment_019_1971_0013, g32p_row02_traceSegment_019_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1944 27 27, g32p_row02_traceSegment_019_1944_0027, g32p_row02_traceSegment_019_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1998 13 14, g32p_row02_traceSegment_019_1998_0013, g32p_row02_traceSegment_019_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2025 13 14, g32p_row02_traceSegment_019_2025_0013, g32p_row02_traceSegment_019_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1998 27 27, g32p_row02_traceSegment_019_1998_0027, g32p_row02_traceSegment_019_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1944 54 54, g32p_row02_traceSegment_019_1944_0054, g32p_row02_traceSegment_019_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2052 13 14, g32p_row02_traceSegment_019_2052_0013, g32p_row02_traceSegment_019_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2079 13 14, g32p_row02_traceSegment_019_2079_0013, g32p_row02_traceSegment_019_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2052 27 27, g32p_row02_traceSegment_019_2052_0027, g32p_row02_traceSegment_019_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2106 13 14, g32p_row02_traceSegment_019_2106_0013, g32p_row02_traceSegment_019_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2133 13 14, g32p_row02_traceSegment_019_2133_0013, g32p_row02_traceSegment_019_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2106 27 27, g32p_row02_traceSegment_019_2106_0027, g32p_row02_traceSegment_019_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2052 54 54, g32p_row02_traceSegment_019_2052_0054, g32p_row02_traceSegment_019_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1944 108 108, g32p_row02_traceSegment_019_1944_0108, g32p_row02_traceSegment_019_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_019 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1728 216 216, g32p_row02_traceSegment_019_1728_0216, g32p_row02_traceSegment_019_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2160 13 14, g32p_row02_traceSegment_019_2160_0013, g32p_row02_traceSegment_019_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2187 13 14, g32p_row02_traceSegment_019_2187_0013, g32p_row02_traceSegment_019_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2160 27 27, g32p_row02_traceSegment_019_2160_0027, g32p_row02_traceSegment_019_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2214 13 14, g32p_row02_traceSegment_019_2214_0013, g32p_row02_traceSegment_019_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2241 13 14, g32p_row02_traceSegment_019_2241_0013, g32p_row02_traceSegment_019_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2214 27 27, g32p_row02_traceSegment_019_2214_0027, g32p_row02_traceSegment_019_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2160 54 54, g32p_row02_traceSegment_019_2160_0054, g32p_row02_traceSegment_019_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2268 13 14, g32p_row02_traceSegment_019_2268_0013, g32p_row02_traceSegment_019_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2295 13 14, g32p_row02_traceSegment_019_2295_0013, g32p_row02_traceSegment_019_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2268 27 27, g32p_row02_traceSegment_019_2268_0027, g32p_row02_traceSegment_019_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2322 13 14, g32p_row02_traceSegment_019_2322_0013, g32p_row02_traceSegment_019_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2349 13 14, g32p_row02_traceSegment_019_2349_0013, g32p_row02_traceSegment_019_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2322 27 27, g32p_row02_traceSegment_019_2322_0027, g32p_row02_traceSegment_019_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2268 54 54, g32p_row02_traceSegment_019_2268_0054, g32p_row02_traceSegment_019_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2160 108 108, g32p_row02_traceSegment_019_2160_0108, g32p_row02_traceSegment_019_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2376 13 14, g32p_row02_traceSegment_019_2376_0013, g32p_row02_traceSegment_019_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2403 13 14, g32p_row02_traceSegment_019_2403_0013, g32p_row02_traceSegment_019_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2376 27 27, g32p_row02_traceSegment_019_2376_0027, g32p_row02_traceSegment_019_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2430 13 14, g32p_row02_traceSegment_019_2430_0013, g32p_row02_traceSegment_019_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2457 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2457 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2457 13 14, g32p_row02_traceSegment_019_2457_0013, g32p_row02_traceSegment_019_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2430 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2430 27 27, g32p_row02_traceSegment_019_2430_0027, g32p_row02_traceSegment_019_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 2376 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2376 54 54, g32p_row02_traceSegment_019_2376_0054, g32p_row02_traceSegment_019_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2484 13 14, g32p_row02_traceSegment_019_2484_0013, g32p_row02_traceSegment_019_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2511 13 14, g32p_row02_traceSegment_019_2511_0013, g32p_row02_traceSegment_019_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2484 27 27, g32p_row02_traceSegment_019_2484_0027, g32p_row02_traceSegment_019_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2538 13 14, g32p_row02_traceSegment_019_2538_0013, g32p_row02_traceSegment_019_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2565 13 14, g32p_row02_traceSegment_019_2565_0013, g32p_row02_traceSegment_019_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2538 27 27, g32p_row02_traceSegment_019_2538_0027, g32p_row02_traceSegment_019_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2484 54 54, g32p_row02_traceSegment_019_2484_0054, g32p_row02_traceSegment_019_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 2376 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2376 108 108, g32p_row02_traceSegment_019_2376_0108, g32p_row02_traceSegment_019_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_019 2160 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2160 216 216, g32p_row02_traceSegment_019_2160_0216, g32p_row02_traceSegment_019_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_019 1728 864 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1728 432 432, g32p_row02_traceSegment_019_1728_0432, g32p_row02_traceSegment_019_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2592 13 14, g32p_row02_traceSegment_019_2592_0013, g32p_row02_traceSegment_019_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2619 13 14, g32p_row02_traceSegment_019_2619_0013, g32p_row02_traceSegment_019_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2592 27 27, g32p_row02_traceSegment_019_2592_0027, g32p_row02_traceSegment_019_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2646 13 14, g32p_row02_traceSegment_019_2646_0013, g32p_row02_traceSegment_019_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2673 13 14, g32p_row02_traceSegment_019_2673_0013, g32p_row02_traceSegment_019_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2646 27 27, g32p_row02_traceSegment_019_2646_0027, g32p_row02_traceSegment_019_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2592 54 54, g32p_row02_traceSegment_019_2592_0054, g32p_row02_traceSegment_019_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2700 13 14, g32p_row02_traceSegment_019_2700_0013, g32p_row02_traceSegment_019_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2727 13 14, g32p_row02_traceSegment_019_2727_0013, g32p_row02_traceSegment_019_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2700 27 27, g32p_row02_traceSegment_019_2700_0027, g32p_row02_traceSegment_019_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2754 13 14, g32p_row02_traceSegment_019_2754_0013, g32p_row02_traceSegment_019_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2781 13 14, g32p_row02_traceSegment_019_2781_0013, g32p_row02_traceSegment_019_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2754 27 27, g32p_row02_traceSegment_019_2754_0027, g32p_row02_traceSegment_019_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2700 54 54, g32p_row02_traceSegment_019_2700_0054, g32p_row02_traceSegment_019_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2592 108 108, g32p_row02_traceSegment_019_2592_0108, g32p_row02_traceSegment_019_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2808 13 14, g32p_row02_traceSegment_019_2808_0013, g32p_row02_traceSegment_019_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2835 13 14, g32p_row02_traceSegment_019_2835_0013, g32p_row02_traceSegment_019_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2808 27 27, g32p_row02_traceSegment_019_2808_0027, g32p_row02_traceSegment_019_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2862 13 14, g32p_row02_traceSegment_019_2862_0013, g32p_row02_traceSegment_019_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2889 13 14, g32p_row02_traceSegment_019_2889_0013, g32p_row02_traceSegment_019_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2862 27 27, g32p_row02_traceSegment_019_2862_0027, g32p_row02_traceSegment_019_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2808 54 54, g32p_row02_traceSegment_019_2808_0054, g32p_row02_traceSegment_019_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2916 13 14, g32p_row02_traceSegment_019_2916_0013, g32p_row02_traceSegment_019_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2943 13 14, g32p_row02_traceSegment_019_2943_0013, g32p_row02_traceSegment_019_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2916 27 27, g32p_row02_traceSegment_019_2916_0027, g32p_row02_traceSegment_019_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2970 13 14, g32p_row02_traceSegment_019_2970_0013, g32p_row02_traceSegment_019_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2997 13 14, g32p_row02_traceSegment_019_2997_0013, g32p_row02_traceSegment_019_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2970 27 27, g32p_row02_traceSegment_019_2970_0027, g32p_row02_traceSegment_019_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2916 54 54, g32p_row02_traceSegment_019_2916_0054, g32p_row02_traceSegment_019_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2808 108 108, g32p_row02_traceSegment_019_2808_0108, g32p_row02_traceSegment_019_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_019 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2592 216 216, g32p_row02_traceSegment_019_2592_0216, g32p_row02_traceSegment_019_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3024 13 14, g32p_row02_traceSegment_019_3024_0013, g32p_row02_traceSegment_019_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3051 13 14, g32p_row02_traceSegment_019_3051_0013, g32p_row02_traceSegment_019_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3024 27 27, g32p_row02_traceSegment_019_3024_0027, g32p_row02_traceSegment_019_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3078 13 14, g32p_row02_traceSegment_019_3078_0013, g32p_row02_traceSegment_019_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3105 13 14, g32p_row02_traceSegment_019_3105_0013, g32p_row02_traceSegment_019_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3078 27 27, g32p_row02_traceSegment_019_3078_0027, g32p_row02_traceSegment_019_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3024 54 54, g32p_row02_traceSegment_019_3024_0054, g32p_row02_traceSegment_019_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3132 13 14, g32p_row02_traceSegment_019_3132_0013, g32p_row02_traceSegment_019_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3159 13 14, g32p_row02_traceSegment_019_3159_0013, g32p_row02_traceSegment_019_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3132 27 27, g32p_row02_traceSegment_019_3132_0027, g32p_row02_traceSegment_019_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3186 13 14, g32p_row02_traceSegment_019_3186_0013, g32p_row02_traceSegment_019_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3213 13 14, g32p_row02_traceSegment_019_3213_0013, g32p_row02_traceSegment_019_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3186 27 27, g32p_row02_traceSegment_019_3186_0027, g32p_row02_traceSegment_019_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3132 54 54, g32p_row02_traceSegment_019_3132_0054, g32p_row02_traceSegment_019_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3024 108 108, g32p_row02_traceSegment_019_3024_0108, g32p_row02_traceSegment_019_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3240 13 14, g32p_row02_traceSegment_019_3240_0013, g32p_row02_traceSegment_019_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3267 13 14, g32p_row02_traceSegment_019_3267_0013, g32p_row02_traceSegment_019_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3240 27 27, g32p_row02_traceSegment_019_3240_0027, g32p_row02_traceSegment_019_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3294 13 14, g32p_row02_traceSegment_019_3294_0013, g32p_row02_traceSegment_019_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3321 13 14, g32p_row02_traceSegment_019_3321_0013, g32p_row02_traceSegment_019_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3294 27 27, g32p_row02_traceSegment_019_3294_0027, g32p_row02_traceSegment_019_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3240 54 54, g32p_row02_traceSegment_019_3240_0054, g32p_row02_traceSegment_019_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3348 13 14, g32p_row02_traceSegment_019_3348_0013, g32p_row02_traceSegment_019_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3375 13 14, g32p_row02_traceSegment_019_3375_0013, g32p_row02_traceSegment_019_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3348 27 27, g32p_row02_traceSegment_019_3348_0027, g32p_row02_traceSegment_019_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3402 13 14, g32p_row02_traceSegment_019_3402_0013, g32p_row02_traceSegment_019_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_019 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_019 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_019_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_019 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3429 13 14, g32p_row02_traceSegment_019_3429_0013, g32p_row02_traceSegment_019_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_019 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3402 27 27, g32p_row02_traceSegment_019_3402_0027, g32p_row02_traceSegment_019_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_019 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3348 54 54, g32p_row02_traceSegment_019_3348_0054, g32p_row02_traceSegment_019_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_019 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3240 108 108, g32p_row02_traceSegment_019_3240_0108, g32p_row02_traceSegment_019_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_019_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_019 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 3024 216 216, g32p_row02_traceSegment_019_3024_0216, g32p_row02_traceSegment_019_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_019_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_019 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 2592 432 432, g32p_row02_traceSegment_019_2592_0432, g32p_row02_traceSegment_019_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_019_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_019 1728 1728 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 1728 864 864, g32p_row02_traceSegment_019_1728_0864, g32p_row02_traceSegment_019_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_019_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_019 0 3456 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_019 0 1728 1728, g32p_row02_traceSegment_019_0000_1728, g32p_row02_traceSegment_019_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 19 = [0, 0, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_019_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 8) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 8) (g32p_literalTraceValue 1 8)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_008]
  decide +kernel

theorem g32p_row02_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 10) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 10) (g32p_literalTraceValue 1 10)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_010]
  decide +kernel

theorem g32p_row02_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 11) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 11) (g32p_literalTraceValue 1 11)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row02_traceCoefficients_011]
  decide +kernel

theorem g32p_row02_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 13) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 13) (g32p_literalTraceValue 1 13)
      [1, -1, 1] [0, 0, 6912, 6912] = true := by
  rw [g32p_row02_traceCoefficients_013]
  decide +kernel

theorem g32p_row02_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 15) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 15) (g32p_literalTraceValue 1 15)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_015]
  decide +kernel

theorem g32p_row02_tracePolynomial_017 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 17) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 17) (g32p_literalTraceValue 1 17)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_017]
  decide +kernel

theorem g32p_row02_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 18) (g32p_literalTraceValue 1 18)
      [1, -1, 1] [41472, 41472] = true := by
  rw [g32p_row02_traceCoefficients_018]
  decide +kernel

theorem g32p_row02_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 19) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 19) (g32p_literalTraceValue 1 19)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_019]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
