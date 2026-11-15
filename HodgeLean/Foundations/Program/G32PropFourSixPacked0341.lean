import HodgeLean.Foundations.Program.G32PropFourSixPacked0335
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0340

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_074 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 74 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_074_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 0 13 14, g32p_row04_traceSegment_074_0000_0013, g32p_row04_traceSegment_074_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 27 13 14, g32p_row04_traceSegment_074_0027_0013, g32p_row04_traceSegment_074_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 0 27 27, g32p_row04_traceSegment_074_0000_0027, g32p_row04_traceSegment_074_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 54 13 14, g32p_row04_traceSegment_074_0054_0013, g32p_row04_traceSegment_074_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 81 13 14, g32p_row04_traceSegment_074_0081_0013, g32p_row04_traceSegment_074_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 54 27 27, g32p_row04_traceSegment_074_0054_0027, g32p_row04_traceSegment_074_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 0 54 54, g32p_row04_traceSegment_074_0000_0054, g32p_row04_traceSegment_074_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 108 13 14, g32p_row04_traceSegment_074_0108_0013, g32p_row04_traceSegment_074_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 135 13 14, g32p_row04_traceSegment_074_0135_0013, g32p_row04_traceSegment_074_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 108 27 27, g32p_row04_traceSegment_074_0108_0027, g32p_row04_traceSegment_074_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 162 13 14, g32p_row04_traceSegment_074_0162_0013, g32p_row04_traceSegment_074_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 189 13 14, g32p_row04_traceSegment_074_0189_0013, g32p_row04_traceSegment_074_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 162 27 27, g32p_row04_traceSegment_074_0162_0027, g32p_row04_traceSegment_074_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 108 54 54, g32p_row04_traceSegment_074_0108_0054, g32p_row04_traceSegment_074_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_074 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 0 108 108, g32p_row04_traceSegment_074_0000_0108, g32p_row04_traceSegment_074_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 216 13 14, g32p_row04_traceSegment_074_0216_0013, g32p_row04_traceSegment_074_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 243 13 14, g32p_row04_traceSegment_074_0243_0013, g32p_row04_traceSegment_074_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 216 27 27, g32p_row04_traceSegment_074_0216_0027, g32p_row04_traceSegment_074_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 270 13 14, g32p_row04_traceSegment_074_0270_0013, g32p_row04_traceSegment_074_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 297 13 14, g32p_row04_traceSegment_074_0297_0013, g32p_row04_traceSegment_074_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 270 27 27, g32p_row04_traceSegment_074_0270_0027, g32p_row04_traceSegment_074_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 216 54 54, g32p_row04_traceSegment_074_0216_0054, g32p_row04_traceSegment_074_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 324 13 14, g32p_row04_traceSegment_074_0324_0013, g32p_row04_traceSegment_074_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 351 13 14, g32p_row04_traceSegment_074_0351_0013, g32p_row04_traceSegment_074_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 324 27 27, g32p_row04_traceSegment_074_0324_0027, g32p_row04_traceSegment_074_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 378 13 14, g32p_row04_traceSegment_074_0378_0013, g32p_row04_traceSegment_074_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 405 13 14, g32p_row04_traceSegment_074_0405_0013, g32p_row04_traceSegment_074_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 378 27 27, g32p_row04_traceSegment_074_0378_0027, g32p_row04_traceSegment_074_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 324 54 54, g32p_row04_traceSegment_074_0324_0054, g32p_row04_traceSegment_074_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_074 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 216 108 108, g32p_row04_traceSegment_074_0216_0108, g32p_row04_traceSegment_074_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_074 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 0 216 216, g32p_row04_traceSegment_074_0000_0216, g32p_row04_traceSegment_074_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 432 13 14, g32p_row04_traceSegment_074_0432_0013, g32p_row04_traceSegment_074_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 459 13 14, g32p_row04_traceSegment_074_0459_0013, g32p_row04_traceSegment_074_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 432 27 27, g32p_row04_traceSegment_074_0432_0027, g32p_row04_traceSegment_074_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 486 13 14, g32p_row04_traceSegment_074_0486_0013, g32p_row04_traceSegment_074_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 513 13 14, g32p_row04_traceSegment_074_0513_0013, g32p_row04_traceSegment_074_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 486 27 27, g32p_row04_traceSegment_074_0486_0027, g32p_row04_traceSegment_074_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 432 54 54, g32p_row04_traceSegment_074_0432_0054, g32p_row04_traceSegment_074_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 540 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 553 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 540 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 540 13 14, g32p_row04_traceSegment_074_0540_0013, g32p_row04_traceSegment_074_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 567 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 580 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 567 27 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 567 13 14, g32p_row04_traceSegment_074_0567_0013, g32p_row04_traceSegment_074_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 540 54 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 540 27 27, g32p_row04_traceSegment_074_0540_0027, g32p_row04_traceSegment_074_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 594 13 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 607 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 594 27 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 594 13 14, g32p_row04_traceSegment_074_0594_0013, g32p_row04_traceSegment_074_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 621 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 634 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 621 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 621 13 14, g32p_row04_traceSegment_074_0621_0013, g32p_row04_traceSegment_074_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 594 54 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 594 27 27, g32p_row04_traceSegment_074_0594_0027, g32p_row04_traceSegment_074_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 540 108 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 540 54 54, g32p_row04_traceSegment_074_0540_0054, g32p_row04_traceSegment_074_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_074 432 216 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 432 108 108, g32p_row04_traceSegment_074_0432_0108, g32p_row04_traceSegment_074_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 648 13 14, g32p_row04_traceSegment_074_0648_0013, g32p_row04_traceSegment_074_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 675 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 688 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 675 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 675 13 14, g32p_row04_traceSegment_074_0675_0013, g32p_row04_traceSegment_074_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 648 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 648 27 27, g32p_row04_traceSegment_074_0648_0027, g32p_row04_traceSegment_074_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 702 13 14, g32p_row04_traceSegment_074_0702_0013, g32p_row04_traceSegment_074_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 729 13 14, g32p_row04_traceSegment_074_0729_0013, g32p_row04_traceSegment_074_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 702 27 27, g32p_row04_traceSegment_074_0702_0027, g32p_row04_traceSegment_074_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 648 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 648 54 54, g32p_row04_traceSegment_074_0648_0054, g32p_row04_traceSegment_074_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 756 13 14, g32p_row04_traceSegment_074_0756_0013, g32p_row04_traceSegment_074_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 783 13 14, g32p_row04_traceSegment_074_0783_0013, g32p_row04_traceSegment_074_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 756 27 27, g32p_row04_traceSegment_074_0756_0027, g32p_row04_traceSegment_074_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 810 13 14, g32p_row04_traceSegment_074_0810_0013, g32p_row04_traceSegment_074_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 837 13 14, g32p_row04_traceSegment_074_0837_0013, g32p_row04_traceSegment_074_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 810 27 27, g32p_row04_traceSegment_074_0810_0027, g32p_row04_traceSegment_074_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 756 54 54, g32p_row04_traceSegment_074_0756_0054, g32p_row04_traceSegment_074_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_074 648 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 648 108 108, g32p_row04_traceSegment_074_0648_0108, g32p_row04_traceSegment_074_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_074 432 432 = [0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 432 216 216, g32p_row04_traceSegment_074_0432_0216, g32p_row04_traceSegment_074_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_074 0 864 = [0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 0 432 432, g32p_row04_traceSegment_074_0000_0432, g32p_row04_traceSegment_074_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 864 13 14, g32p_row04_traceSegment_074_0864_0013, g32p_row04_traceSegment_074_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 891 13 14, g32p_row04_traceSegment_074_0891_0013, g32p_row04_traceSegment_074_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 864 27 27, g32p_row04_traceSegment_074_0864_0027, g32p_row04_traceSegment_074_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 918 13 14, g32p_row04_traceSegment_074_0918_0013, g32p_row04_traceSegment_074_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 945 13 14, g32p_row04_traceSegment_074_0945_0013, g32p_row04_traceSegment_074_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 918 27 27, g32p_row04_traceSegment_074_0918_0027, g32p_row04_traceSegment_074_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 864 54 54, g32p_row04_traceSegment_074_0864_0054, g32p_row04_traceSegment_074_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 972 13 14, g32p_row04_traceSegment_074_0972_0013, g32p_row04_traceSegment_074_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 999 13 14, g32p_row04_traceSegment_074_0999_0013, g32p_row04_traceSegment_074_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 972 27 27, g32p_row04_traceSegment_074_0972_0027, g32p_row04_traceSegment_074_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1026 13 14, g32p_row04_traceSegment_074_1026_0013, g32p_row04_traceSegment_074_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1053 13 14, g32p_row04_traceSegment_074_1053_0013, g32p_row04_traceSegment_074_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1026 27 27, g32p_row04_traceSegment_074_1026_0027, g32p_row04_traceSegment_074_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 972 54 54, g32p_row04_traceSegment_074_0972_0054, g32p_row04_traceSegment_074_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_074 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 864 108 108, g32p_row04_traceSegment_074_0864_0108, g32p_row04_traceSegment_074_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1080 13 14, g32p_row04_traceSegment_074_1080_0013, g32p_row04_traceSegment_074_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1107 13 14, g32p_row04_traceSegment_074_1107_0013, g32p_row04_traceSegment_074_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1080 27 27, g32p_row04_traceSegment_074_1080_0027, g32p_row04_traceSegment_074_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1134 13 14, g32p_row04_traceSegment_074_1134_0013, g32p_row04_traceSegment_074_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1161 13 14, g32p_row04_traceSegment_074_1161_0013, g32p_row04_traceSegment_074_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1134 27 27, g32p_row04_traceSegment_074_1134_0027, g32p_row04_traceSegment_074_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1080 54 54, g32p_row04_traceSegment_074_1080_0054, g32p_row04_traceSegment_074_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1188 13 14, g32p_row04_traceSegment_074_1188_0013, g32p_row04_traceSegment_074_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1215 13 14, g32p_row04_traceSegment_074_1215_0013, g32p_row04_traceSegment_074_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1188 27 27, g32p_row04_traceSegment_074_1188_0027, g32p_row04_traceSegment_074_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1242 13 14, g32p_row04_traceSegment_074_1242_0013, g32p_row04_traceSegment_074_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1269 13 14, g32p_row04_traceSegment_074_1269_0013, g32p_row04_traceSegment_074_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1242 27 27, g32p_row04_traceSegment_074_1242_0027, g32p_row04_traceSegment_074_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1188 54 54, g32p_row04_traceSegment_074_1188_0054, g32p_row04_traceSegment_074_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_074 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1080 108 108, g32p_row04_traceSegment_074_1080_0108, g32p_row04_traceSegment_074_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_074 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 864 216 216, g32p_row04_traceSegment_074_0864_0216, g32p_row04_traceSegment_074_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1296 13 14, g32p_row04_traceSegment_074_1296_0013, g32p_row04_traceSegment_074_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1323 13 14, g32p_row04_traceSegment_074_1323_0013, g32p_row04_traceSegment_074_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1296 27 27, g32p_row04_traceSegment_074_1296_0027, g32p_row04_traceSegment_074_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1350 13 14, g32p_row04_traceSegment_074_1350_0013, g32p_row04_traceSegment_074_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1377 13 14, g32p_row04_traceSegment_074_1377_0013, g32p_row04_traceSegment_074_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1350 27 27, g32p_row04_traceSegment_074_1350_0027, g32p_row04_traceSegment_074_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1296 54 54, g32p_row04_traceSegment_074_1296_0054, g32p_row04_traceSegment_074_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1404 13 14, g32p_row04_traceSegment_074_1404_0013, g32p_row04_traceSegment_074_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1431 13 14, g32p_row04_traceSegment_074_1431_0013, g32p_row04_traceSegment_074_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1404 27 27, g32p_row04_traceSegment_074_1404_0027, g32p_row04_traceSegment_074_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1458 13 14, g32p_row04_traceSegment_074_1458_0013, g32p_row04_traceSegment_074_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1485 13 14, g32p_row04_traceSegment_074_1485_0013, g32p_row04_traceSegment_074_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1458 27 27, g32p_row04_traceSegment_074_1458_0027, g32p_row04_traceSegment_074_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1404 54 54, g32p_row04_traceSegment_074_1404_0054, g32p_row04_traceSegment_074_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_074 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1296 108 108, g32p_row04_traceSegment_074_1296_0108, g32p_row04_traceSegment_074_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1525 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1512 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1512 13 14, g32p_row04_traceSegment_074_1512_0013, g32p_row04_traceSegment_074_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1539 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1552 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1539 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1539 13 14, g32p_row04_traceSegment_074_1539_0013, g32p_row04_traceSegment_074_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1512 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1512 27 27, g32p_row04_traceSegment_074_1512_0027, g32p_row04_traceSegment_074_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1566 13 14, g32p_row04_traceSegment_074_1566_0013, g32p_row04_traceSegment_074_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1606 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1593 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1593 13 14, g32p_row04_traceSegment_074_1593_0013, g32p_row04_traceSegment_074_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1566 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1566 27 27, g32p_row04_traceSegment_074_1566_0027, g32p_row04_traceSegment_074_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 1512 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1512 54 54, g32p_row04_traceSegment_074_1512_0054, g32p_row04_traceSegment_074_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1620 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1633 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1620 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1620 13 14, g32p_row04_traceSegment_074_1620_0013, g32p_row04_traceSegment_074_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1647 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1660 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1647 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1647 13 14, g32p_row04_traceSegment_074_1647_0013, g32p_row04_traceSegment_074_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1620 54 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1620 27 27, g32p_row04_traceSegment_074_1620_0027, g32p_row04_traceSegment_074_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1674 13 14, g32p_row04_traceSegment_074_1674_0013, g32p_row04_traceSegment_074_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_074 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_074 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_074_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_074 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1701 13 14, g32p_row04_traceSegment_074_1701_0013, g32p_row04_traceSegment_074_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_074 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1674 27 27, g32p_row04_traceSegment_074_1674_0027, g32p_row04_traceSegment_074_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_074 1620 108 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1620 54 54, g32p_row04_traceSegment_074_1620_0054, g32p_row04_traceSegment_074_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_074 1512 216 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1512 108 108, g32p_row04_traceSegment_074_1512_0108, g32p_row04_traceSegment_074_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_074_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_074 1296 432 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 1296 216 216, g32p_row04_traceSegment_074_1296_0216, g32p_row04_traceSegment_074_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_074 864 864 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 864 432 432, g32p_row04_traceSegment_074_0864_0432, g32p_row04_traceSegment_074_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_074_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_074 0 1728 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_074 0 864 864, g32p_row04_traceSegment_074_0000_0864, g32p_row04_traceSegment_074_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 74 = [0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_074_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_075 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 75 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_075_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 13 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 0 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 0 13 14, g32p_row04_traceSegment_075_0000_0013, g32p_row04_traceSegment_075_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 27 13 14, g32p_row04_traceSegment_075_0027_0013, g32p_row04_traceSegment_075_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 0 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 0 27 27, g32p_row04_traceSegment_075_0000_0027, g32p_row04_traceSegment_075_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 54 13 14, g32p_row04_traceSegment_075_0054_0013, g32p_row04_traceSegment_075_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 81 13 14, g32p_row04_traceSegment_075_0081_0013, g32p_row04_traceSegment_075_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 54 27 27, g32p_row04_traceSegment_075_0054_0027, g32p_row04_traceSegment_075_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 0 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 0 54 54, g32p_row04_traceSegment_075_0000_0054, g32p_row04_traceSegment_075_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 108 13 14, g32p_row04_traceSegment_075_0108_0013, g32p_row04_traceSegment_075_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 148 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 135 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 135 13 14, g32p_row04_traceSegment_075_0135_0013, g32p_row04_traceSegment_075_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 108 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 108 27 27, g32p_row04_traceSegment_075_0108_0027, g32p_row04_traceSegment_075_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 162 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 162 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 162 13 14, g32p_row04_traceSegment_075_0162_0013, g32p_row04_traceSegment_075_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 189 13 14, g32p_row04_traceSegment_075_0189_0013, g32p_row04_traceSegment_075_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 162 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 162 27 27, g32p_row04_traceSegment_075_0162_0027, g32p_row04_traceSegment_075_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 108 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 108 54 54, g32p_row04_traceSegment_075_0108_0054, g32p_row04_traceSegment_075_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_075 0 216 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 0 108 108, g32p_row04_traceSegment_075_0000_0108, g32p_row04_traceSegment_075_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 216 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 216 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 216 13 14, g32p_row04_traceSegment_075_0216_0013, g32p_row04_traceSegment_075_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 256 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 243 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 243 13 14, g32p_row04_traceSegment_075_0243_0013, g32p_row04_traceSegment_075_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 216 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 216 27 27, g32p_row04_traceSegment_075_0216_0027, g32p_row04_traceSegment_075_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 270 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 270 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 270 13 14, g32p_row04_traceSegment_075_0270_0013, g32p_row04_traceSegment_075_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 297 13 14, g32p_row04_traceSegment_075_0297_0013, g32p_row04_traceSegment_075_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 270 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 270 27 27, g32p_row04_traceSegment_075_0270_0027, g32p_row04_traceSegment_075_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 216 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 216 54 54, g32p_row04_traceSegment_075_0216_0054, g32p_row04_traceSegment_075_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 324 13 14, g32p_row04_traceSegment_075_0324_0013, g32p_row04_traceSegment_075_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 351 13 14, g32p_row04_traceSegment_075_0351_0013, g32p_row04_traceSegment_075_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 324 27 27, g32p_row04_traceSegment_075_0324_0027, g32p_row04_traceSegment_075_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 378 13 14, g32p_row04_traceSegment_075_0378_0013, g32p_row04_traceSegment_075_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 405 13 14, g32p_row04_traceSegment_075_0405_0013, g32p_row04_traceSegment_075_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 378 27 27, g32p_row04_traceSegment_075_0378_0027, g32p_row04_traceSegment_075_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 324 54 54, g32p_row04_traceSegment_075_0324_0054, g32p_row04_traceSegment_075_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_075 216 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 216 108 108, g32p_row04_traceSegment_075_0216_0108, g32p_row04_traceSegment_075_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_075 0 432 = [0, 2, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 0 216 216, g32p_row04_traceSegment_075_0000_0216, g32p_row04_traceSegment_075_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 432 13 14, g32p_row04_traceSegment_075_0432_0013, g32p_row04_traceSegment_075_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 459 13 14, g32p_row04_traceSegment_075_0459_0013, g32p_row04_traceSegment_075_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 432 27 27, g32p_row04_traceSegment_075_0432_0027, g32p_row04_traceSegment_075_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 486 13 14, g32p_row04_traceSegment_075_0486_0013, g32p_row04_traceSegment_075_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 513 13 14, g32p_row04_traceSegment_075_0513_0013, g32p_row04_traceSegment_075_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 486 27 27, g32p_row04_traceSegment_075_0486_0027, g32p_row04_traceSegment_075_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 432 54 54, g32p_row04_traceSegment_075_0432_0054, g32p_row04_traceSegment_075_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 540 13 14, g32p_row04_traceSegment_075_0540_0013, g32p_row04_traceSegment_075_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 567 13 14, g32p_row04_traceSegment_075_0567_0013, g32p_row04_traceSegment_075_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 540 27 27, g32p_row04_traceSegment_075_0540_0027, g32p_row04_traceSegment_075_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 594 13 14, g32p_row04_traceSegment_075_0594_0013, g32p_row04_traceSegment_075_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 621 13 14, g32p_row04_traceSegment_075_0621_0013, g32p_row04_traceSegment_075_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 594 27 27, g32p_row04_traceSegment_075_0594_0027, g32p_row04_traceSegment_075_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 540 54 54, g32p_row04_traceSegment_075_0540_0054, g32p_row04_traceSegment_075_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_075 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 432 108 108, g32p_row04_traceSegment_075_0432_0108, g32p_row04_traceSegment_075_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 648 13 14, g32p_row04_traceSegment_075_0648_0013, g32p_row04_traceSegment_075_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 675 13 14, g32p_row04_traceSegment_075_0675_0013, g32p_row04_traceSegment_075_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 648 27 27, g32p_row04_traceSegment_075_0648_0027, g32p_row04_traceSegment_075_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 702 13 14, g32p_row04_traceSegment_075_0702_0013, g32p_row04_traceSegment_075_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 729 13 14, g32p_row04_traceSegment_075_0729_0013, g32p_row04_traceSegment_075_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 702 27 27, g32p_row04_traceSegment_075_0702_0027, g32p_row04_traceSegment_075_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 648 54 54, g32p_row04_traceSegment_075_0648_0054, g32p_row04_traceSegment_075_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 756 13 14, g32p_row04_traceSegment_075_0756_0013, g32p_row04_traceSegment_075_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 783 13 14, g32p_row04_traceSegment_075_0783_0013, g32p_row04_traceSegment_075_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 756 27 27, g32p_row04_traceSegment_075_0756_0027, g32p_row04_traceSegment_075_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 810 13 14, g32p_row04_traceSegment_075_0810_0013, g32p_row04_traceSegment_075_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 837 13 14, g32p_row04_traceSegment_075_0837_0013, g32p_row04_traceSegment_075_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 810 27 27, g32p_row04_traceSegment_075_0810_0027, g32p_row04_traceSegment_075_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 756 54 54, g32p_row04_traceSegment_075_0756_0054, g32p_row04_traceSegment_075_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_075 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 648 108 108, g32p_row04_traceSegment_075_0648_0108, g32p_row04_traceSegment_075_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_075 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 432 216 216, g32p_row04_traceSegment_075_0432_0216, g32p_row04_traceSegment_075_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_075 0 864 = [0, 2, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 0 432 432, g32p_row04_traceSegment_075_0000_0432, g32p_row04_traceSegment_075_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 864 13 14, g32p_row04_traceSegment_075_0864_0013, g32p_row04_traceSegment_075_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 891 13 14, g32p_row04_traceSegment_075_0891_0013, g32p_row04_traceSegment_075_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 864 27 27, g32p_row04_traceSegment_075_0864_0027, g32p_row04_traceSegment_075_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 931 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 918 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 918 13 14, g32p_row04_traceSegment_075_0918_0013, g32p_row04_traceSegment_075_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 945 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 958 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 945 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 945 13 14, g32p_row04_traceSegment_075_0945_0013, g32p_row04_traceSegment_075_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 918 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 918 27 27, g32p_row04_traceSegment_075_0918_0027, g32p_row04_traceSegment_075_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 864 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 864 54 54, g32p_row04_traceSegment_075_0864_0054, g32p_row04_traceSegment_075_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 972 13 14, g32p_row04_traceSegment_075_0972_0013, g32p_row04_traceSegment_075_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 999 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1012 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 999 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 999 13 14, g32p_row04_traceSegment_075_0999_0013, g32p_row04_traceSegment_075_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 972 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 972 27 27, g32p_row04_traceSegment_075_0972_0027, g32p_row04_traceSegment_075_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1026 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1026 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1026 13 14, g32p_row04_traceSegment_075_1026_0013, g32p_row04_traceSegment_075_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1066 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1053 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1053 13 14, g32p_row04_traceSegment_075_1053_0013, g32p_row04_traceSegment_075_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1026 54 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1026 27 27, g32p_row04_traceSegment_075_1026_0027, g32p_row04_traceSegment_075_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 972 108 = [0, 5, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 972 54 54, g32p_row04_traceSegment_075_0972_0054, g32p_row04_traceSegment_075_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_075 864 216 = [0, 9, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 864 108 108, g32p_row04_traceSegment_075_0864_0108, g32p_row04_traceSegment_075_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1080 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1093 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1080 27 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1080 13 14, g32p_row04_traceSegment_075_1080_0013, g32p_row04_traceSegment_075_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1107 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1107 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1107 13 14, g32p_row04_traceSegment_075_1107_0013, g32p_row04_traceSegment_075_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1080 54 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1080 27 27, g32p_row04_traceSegment_075_1080_0027, g32p_row04_traceSegment_075_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1134 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1134 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1134 13 14, g32p_row04_traceSegment_075_1134_0013, g32p_row04_traceSegment_075_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1161 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1174 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1161 27 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1161 13 14, g32p_row04_traceSegment_075_1161_0013, g32p_row04_traceSegment_075_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1134 54 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1134 27 27, g32p_row04_traceSegment_075_1134_0027, g32p_row04_traceSegment_075_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 1080 108 = [0, 3, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1080 54 54, g32p_row04_traceSegment_075_1080_0054, g32p_row04_traceSegment_075_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1188 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1188 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1188 13 14, g32p_row04_traceSegment_075_1188_0013, g32p_row04_traceSegment_075_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1215 13 14, g32p_row04_traceSegment_075_1215_0013, g32p_row04_traceSegment_075_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1188 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1188 27 27, g32p_row04_traceSegment_075_1188_0027, g32p_row04_traceSegment_075_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1242 13 14, g32p_row04_traceSegment_075_1242_0013, g32p_row04_traceSegment_075_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1269 13 14, g32p_row04_traceSegment_075_1269_0013, g32p_row04_traceSegment_075_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1242 27 27, g32p_row04_traceSegment_075_1242_0027, g32p_row04_traceSegment_075_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 1188 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1188 54 54, g32p_row04_traceSegment_075_1188_0054, g32p_row04_traceSegment_075_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_075 1080 216 = [0, 3, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1080 108 108, g32p_row04_traceSegment_075_1080_0108, g32p_row04_traceSegment_075_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_075 864 432 = [0, 12, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 864 216 216, g32p_row04_traceSegment_075_0864_0216, g32p_row04_traceSegment_075_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1296 13 14, g32p_row04_traceSegment_075_1296_0013, g32p_row04_traceSegment_075_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1323 13 14, g32p_row04_traceSegment_075_1323_0013, g32p_row04_traceSegment_075_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1296 27 27, g32p_row04_traceSegment_075_1296_0027, g32p_row04_traceSegment_075_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1350 13 14, g32p_row04_traceSegment_075_1350_0013, g32p_row04_traceSegment_075_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1377 13 14, g32p_row04_traceSegment_075_1377_0013, g32p_row04_traceSegment_075_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1350 27 27, g32p_row04_traceSegment_075_1350_0027, g32p_row04_traceSegment_075_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1296 54 54, g32p_row04_traceSegment_075_1296_0054, g32p_row04_traceSegment_075_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1404 13 14, g32p_row04_traceSegment_075_1404_0013, g32p_row04_traceSegment_075_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1431 13 14, g32p_row04_traceSegment_075_1431_0013, g32p_row04_traceSegment_075_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1404 27 27, g32p_row04_traceSegment_075_1404_0027, g32p_row04_traceSegment_075_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1458 13 14, g32p_row04_traceSegment_075_1458_0013, g32p_row04_traceSegment_075_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1485 13 14, g32p_row04_traceSegment_075_1485_0013, g32p_row04_traceSegment_075_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1458 27 27, g32p_row04_traceSegment_075_1458_0027, g32p_row04_traceSegment_075_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1404 54 54, g32p_row04_traceSegment_075_1404_0054, g32p_row04_traceSegment_075_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_075 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1296 108 108, g32p_row04_traceSegment_075_1296_0108, g32p_row04_traceSegment_075_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1512 13 14, g32p_row04_traceSegment_075_1512_0013, g32p_row04_traceSegment_075_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1539 13 14, g32p_row04_traceSegment_075_1539_0013, g32p_row04_traceSegment_075_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1512 27 27, g32p_row04_traceSegment_075_1512_0027, g32p_row04_traceSegment_075_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1566 13 14, g32p_row04_traceSegment_075_1566_0013, g32p_row04_traceSegment_075_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1593 13 14, g32p_row04_traceSegment_075_1593_0013, g32p_row04_traceSegment_075_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1566 27 27, g32p_row04_traceSegment_075_1566_0027, g32p_row04_traceSegment_075_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1512 54 54, g32p_row04_traceSegment_075_1512_0054, g32p_row04_traceSegment_075_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1620 13 14, g32p_row04_traceSegment_075_1620_0013, g32p_row04_traceSegment_075_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1647 13 14, g32p_row04_traceSegment_075_1647_0013, g32p_row04_traceSegment_075_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1620 27 27, g32p_row04_traceSegment_075_1620_0027, g32p_row04_traceSegment_075_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1674 13 14, g32p_row04_traceSegment_075_1674_0013, g32p_row04_traceSegment_075_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_075 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_075 1714 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_075_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_075 1701 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1701 13 14, g32p_row04_traceSegment_075_1701_0013, g32p_row04_traceSegment_075_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_075 1674 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1674 27 27, g32p_row04_traceSegment_075_1674_0027, g32p_row04_traceSegment_075_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_075 1620 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1620 54 54, g32p_row04_traceSegment_075_1620_0054, g32p_row04_traceSegment_075_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_075 1512 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1512 108 108, g32p_row04_traceSegment_075_1512_0108, g32p_row04_traceSegment_075_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_075_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_075 1296 432 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 1296 216 216, g32p_row04_traceSegment_075_1296_0216, g32p_row04_traceSegment_075_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_075 864 864 = [0, 14, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 864 432 432, g32p_row04_traceSegment_075_0864_0432, g32p_row04_traceSegment_075_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_075_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_075 0 1728 = [0, 16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_075 0 864 864, g32p_row04_traceSegment_075_0000_0864, g32p_row04_traceSegment_075_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 75 = [0, 16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_075_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_076 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 76 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_076_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 0 13 14, g32p_row04_traceSegment_076_0000_0013, g32p_row04_traceSegment_076_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 27 13 14, g32p_row04_traceSegment_076_0027_0013, g32p_row04_traceSegment_076_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 0 27 27, g32p_row04_traceSegment_076_0000_0027, g32p_row04_traceSegment_076_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 54 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 54 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 54 13 14, g32p_row04_traceSegment_076_0054_0013, g32p_row04_traceSegment_076_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 81 13 14, g32p_row04_traceSegment_076_0081_0013, g32p_row04_traceSegment_076_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 54 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 54 27 27, g32p_row04_traceSegment_076_0054_0027, g32p_row04_traceSegment_076_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 0 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 0 54 54, g32p_row04_traceSegment_076_0000_0054, g32p_row04_traceSegment_076_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 108 13 14, g32p_row04_traceSegment_076_0108_0013, g32p_row04_traceSegment_076_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 135 13 14, g32p_row04_traceSegment_076_0135_0013, g32p_row04_traceSegment_076_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 108 27 27, g32p_row04_traceSegment_076_0108_0027, g32p_row04_traceSegment_076_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 162 13 14, g32p_row04_traceSegment_076_0162_0013, g32p_row04_traceSegment_076_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 189 13 14, g32p_row04_traceSegment_076_0189_0013, g32p_row04_traceSegment_076_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 162 27 27, g32p_row04_traceSegment_076_0162_0027, g32p_row04_traceSegment_076_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 108 54 54, g32p_row04_traceSegment_076_0108_0054, g32p_row04_traceSegment_076_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_076 0 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 0 108 108, g32p_row04_traceSegment_076_0000_0108, g32p_row04_traceSegment_076_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 216 13 14, g32p_row04_traceSegment_076_0216_0013, g32p_row04_traceSegment_076_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 243 13 14, g32p_row04_traceSegment_076_0243_0013, g32p_row04_traceSegment_076_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 216 27 27, g32p_row04_traceSegment_076_0216_0027, g32p_row04_traceSegment_076_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 283 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 270 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 270 13 14, g32p_row04_traceSegment_076_0270_0013, g32p_row04_traceSegment_076_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 297 13 14, g32p_row04_traceSegment_076_0297_0013, g32p_row04_traceSegment_076_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 270 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 270 27 27, g32p_row04_traceSegment_076_0270_0027, g32p_row04_traceSegment_076_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 216 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 216 54 54, g32p_row04_traceSegment_076_0216_0054, g32p_row04_traceSegment_076_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 337 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 324 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 324 13 14, g32p_row04_traceSegment_076_0324_0013, g32p_row04_traceSegment_076_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 351 13 14, g32p_row04_traceSegment_076_0351_0013, g32p_row04_traceSegment_076_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 324 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 324 27 27, g32p_row04_traceSegment_076_0324_0027, g32p_row04_traceSegment_076_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 391 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 378 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 378 13 14, g32p_row04_traceSegment_076_0378_0013, g32p_row04_traceSegment_076_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 418 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 405 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 405 13 14, g32p_row04_traceSegment_076_0405_0013, g32p_row04_traceSegment_076_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 378 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 378 27 27, g32p_row04_traceSegment_076_0378_0027, g32p_row04_traceSegment_076_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 324 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 324 54 54, g32p_row04_traceSegment_076_0324_0054, g32p_row04_traceSegment_076_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_076 216 216 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 216 108 108, g32p_row04_traceSegment_076_0216_0108, g32p_row04_traceSegment_076_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_076 0 432 = [2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 0 216 216, g32p_row04_traceSegment_076_0000_0216, g32p_row04_traceSegment_076_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 432 13 14, g32p_row04_traceSegment_076_0432_0013, g32p_row04_traceSegment_076_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 459 13 14, g32p_row04_traceSegment_076_0459_0013, g32p_row04_traceSegment_076_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 432 27 27, g32p_row04_traceSegment_076_0432_0027, g32p_row04_traceSegment_076_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 486 13 14, g32p_row04_traceSegment_076_0486_0013, g32p_row04_traceSegment_076_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 513 13 14, g32p_row04_traceSegment_076_0513_0013, g32p_row04_traceSegment_076_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 486 27 27, g32p_row04_traceSegment_076_0486_0027, g32p_row04_traceSegment_076_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 432 54 54, g32p_row04_traceSegment_076_0432_0054, g32p_row04_traceSegment_076_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 540 13 14, g32p_row04_traceSegment_076_0540_0013, g32p_row04_traceSegment_076_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 567 13 14, g32p_row04_traceSegment_076_0567_0013, g32p_row04_traceSegment_076_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 540 27 27, g32p_row04_traceSegment_076_0540_0027, g32p_row04_traceSegment_076_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 594 13 14, g32p_row04_traceSegment_076_0594_0013, g32p_row04_traceSegment_076_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 621 13 14, g32p_row04_traceSegment_076_0621_0013, g32p_row04_traceSegment_076_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 594 27 27, g32p_row04_traceSegment_076_0594_0027, g32p_row04_traceSegment_076_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 540 54 54, g32p_row04_traceSegment_076_0540_0054, g32p_row04_traceSegment_076_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_076 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 432 108 108, g32p_row04_traceSegment_076_0432_0108, g32p_row04_traceSegment_076_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 648 13 14, g32p_row04_traceSegment_076_0648_0013, g32p_row04_traceSegment_076_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 675 13 14, g32p_row04_traceSegment_076_0675_0013, g32p_row04_traceSegment_076_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 648 27 27, g32p_row04_traceSegment_076_0648_0027, g32p_row04_traceSegment_076_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 702 13 14, g32p_row04_traceSegment_076_0702_0013, g32p_row04_traceSegment_076_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 729 13 14, g32p_row04_traceSegment_076_0729_0013, g32p_row04_traceSegment_076_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 702 27 27, g32p_row04_traceSegment_076_0702_0027, g32p_row04_traceSegment_076_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 648 54 54, g32p_row04_traceSegment_076_0648_0054, g32p_row04_traceSegment_076_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 756 13 14, g32p_row04_traceSegment_076_0756_0013, g32p_row04_traceSegment_076_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 783 13 14, g32p_row04_traceSegment_076_0783_0013, g32p_row04_traceSegment_076_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 756 27 27, g32p_row04_traceSegment_076_0756_0027, g32p_row04_traceSegment_076_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 810 13 14, g32p_row04_traceSegment_076_0810_0013, g32p_row04_traceSegment_076_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 837 13 14, g32p_row04_traceSegment_076_0837_0013, g32p_row04_traceSegment_076_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 810 27 27, g32p_row04_traceSegment_076_0810_0027, g32p_row04_traceSegment_076_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 756 54 54, g32p_row04_traceSegment_076_0756_0054, g32p_row04_traceSegment_076_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_076 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 648 108 108, g32p_row04_traceSegment_076_0648_0108, g32p_row04_traceSegment_076_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_076 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 432 216 216, g32p_row04_traceSegment_076_0432_0216, g32p_row04_traceSegment_076_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_076 0 864 = [2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 0 432 432, g32p_row04_traceSegment_076_0000_0432, g32p_row04_traceSegment_076_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 864 13 14, g32p_row04_traceSegment_076_0864_0013, g32p_row04_traceSegment_076_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 891 13 14, g32p_row04_traceSegment_076_0891_0013, g32p_row04_traceSegment_076_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 864 27 27, g32p_row04_traceSegment_076_0864_0027, g32p_row04_traceSegment_076_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 918 13 14, g32p_row04_traceSegment_076_0918_0013, g32p_row04_traceSegment_076_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 945 13 14, g32p_row04_traceSegment_076_0945_0013, g32p_row04_traceSegment_076_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 918 27 27, g32p_row04_traceSegment_076_0918_0027, g32p_row04_traceSegment_076_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 864 54 54, g32p_row04_traceSegment_076_0864_0054, g32p_row04_traceSegment_076_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 972 13 14, g32p_row04_traceSegment_076_0972_0013, g32p_row04_traceSegment_076_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 999 13 14, g32p_row04_traceSegment_076_0999_0013, g32p_row04_traceSegment_076_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 972 27 27, g32p_row04_traceSegment_076_0972_0027, g32p_row04_traceSegment_076_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1026 13 14, g32p_row04_traceSegment_076_1026_0013, g32p_row04_traceSegment_076_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1053 13 14, g32p_row04_traceSegment_076_1053_0013, g32p_row04_traceSegment_076_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1026 27 27, g32p_row04_traceSegment_076_1026_0027, g32p_row04_traceSegment_076_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 972 54 54, g32p_row04_traceSegment_076_0972_0054, g32p_row04_traceSegment_076_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_076 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 864 108 108, g32p_row04_traceSegment_076_0864_0108, g32p_row04_traceSegment_076_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1080 13 14, g32p_row04_traceSegment_076_1080_0013, g32p_row04_traceSegment_076_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1107 13 14, g32p_row04_traceSegment_076_1107_0013, g32p_row04_traceSegment_076_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1080 27 27, g32p_row04_traceSegment_076_1080_0027, g32p_row04_traceSegment_076_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1134 13 14, g32p_row04_traceSegment_076_1134_0013, g32p_row04_traceSegment_076_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1161 13 14, g32p_row04_traceSegment_076_1161_0013, g32p_row04_traceSegment_076_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1134 27 27, g32p_row04_traceSegment_076_1134_0027, g32p_row04_traceSegment_076_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1080 54 54, g32p_row04_traceSegment_076_1080_0054, g32p_row04_traceSegment_076_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1188 13 14, g32p_row04_traceSegment_076_1188_0013, g32p_row04_traceSegment_076_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1215 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1215 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1215 13 14, g32p_row04_traceSegment_076_1215_0013, g32p_row04_traceSegment_076_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1188 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1188 27 27, g32p_row04_traceSegment_076_1188_0027, g32p_row04_traceSegment_076_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1242 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1242 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1242 13 14, g32p_row04_traceSegment_076_1242_0013, g32p_row04_traceSegment_076_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1269 13 14, g32p_row04_traceSegment_076_1269_0013, g32p_row04_traceSegment_076_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1242 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1242 27 27, g32p_row04_traceSegment_076_1242_0027, g32p_row04_traceSegment_076_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 1188 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1188 54 54, g32p_row04_traceSegment_076_1188_0054, g32p_row04_traceSegment_076_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_076 1080 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1080 108 108, g32p_row04_traceSegment_076_1080_0108, g32p_row04_traceSegment_076_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_076 864 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 864 216 216, g32p_row04_traceSegment_076_0864_0216, g32p_row04_traceSegment_076_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1296 13 14, g32p_row04_traceSegment_076_1296_0013, g32p_row04_traceSegment_076_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1323 13 14, g32p_row04_traceSegment_076_1323_0013, g32p_row04_traceSegment_076_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1296 27 27, g32p_row04_traceSegment_076_1296_0027, g32p_row04_traceSegment_076_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1350 13 14, g32p_row04_traceSegment_076_1350_0013, g32p_row04_traceSegment_076_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1377 13 14, g32p_row04_traceSegment_076_1377_0013, g32p_row04_traceSegment_076_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1350 27 27, g32p_row04_traceSegment_076_1350_0027, g32p_row04_traceSegment_076_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1296 54 54, g32p_row04_traceSegment_076_1296_0054, g32p_row04_traceSegment_076_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1404 13 14, g32p_row04_traceSegment_076_1404_0013, g32p_row04_traceSegment_076_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1431 13 14, g32p_row04_traceSegment_076_1431_0013, g32p_row04_traceSegment_076_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1404 27 27, g32p_row04_traceSegment_076_1404_0027, g32p_row04_traceSegment_076_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1458 13 14, g32p_row04_traceSegment_076_1458_0013, g32p_row04_traceSegment_076_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1485 13 14, g32p_row04_traceSegment_076_1485_0013, g32p_row04_traceSegment_076_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1458 27 27, g32p_row04_traceSegment_076_1458_0027, g32p_row04_traceSegment_076_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1404 54 54, g32p_row04_traceSegment_076_1404_0054, g32p_row04_traceSegment_076_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_076 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1296 108 108, g32p_row04_traceSegment_076_1296_0108, g32p_row04_traceSegment_076_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1512 13 14, g32p_row04_traceSegment_076_1512_0013, g32p_row04_traceSegment_076_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1539 13 14, g32p_row04_traceSegment_076_1539_0013, g32p_row04_traceSegment_076_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1512 27 27, g32p_row04_traceSegment_076_1512_0027, g32p_row04_traceSegment_076_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1566 13 14, g32p_row04_traceSegment_076_1566_0013, g32p_row04_traceSegment_076_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1593 13 14, g32p_row04_traceSegment_076_1593_0013, g32p_row04_traceSegment_076_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1566 27 27, g32p_row04_traceSegment_076_1566_0027, g32p_row04_traceSegment_076_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1512 54 54, g32p_row04_traceSegment_076_1512_0054, g32p_row04_traceSegment_076_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1620 13 14, g32p_row04_traceSegment_076_1620_0013, g32p_row04_traceSegment_076_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1647 13 14, g32p_row04_traceSegment_076_1647_0013, g32p_row04_traceSegment_076_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1620 27 27, g32p_row04_traceSegment_076_1620_0027, g32p_row04_traceSegment_076_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1674 13 14, g32p_row04_traceSegment_076_1674_0013, g32p_row04_traceSegment_076_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_076 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_076 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_076_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_076 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1701 13 14, g32p_row04_traceSegment_076_1701_0013, g32p_row04_traceSegment_076_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_076 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1674 27 27, g32p_row04_traceSegment_076_1674_0027, g32p_row04_traceSegment_076_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_076 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1620 54 54, g32p_row04_traceSegment_076_1620_0054, g32p_row04_traceSegment_076_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_076 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1512 108 108, g32p_row04_traceSegment_076_1512_0108, g32p_row04_traceSegment_076_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_076_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_076 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 1296 216 216, g32p_row04_traceSegment_076_1296_0216, g32p_row04_traceSegment_076_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_076 864 864 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 864 432 432, g32p_row04_traceSegment_076_0864_0432, g32p_row04_traceSegment_076_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_076_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_076 0 1728 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_076 0 864 864, g32p_row04_traceSegment_076_0000_0864, g32p_row04_traceSegment_076_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 76 = [4, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_076_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_077 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 77 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_077_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 0 13 14, g32p_row04_traceSegment_077_0000_0013, g32p_row04_traceSegment_077_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 27 13 14, g32p_row04_traceSegment_077_0027_0013, g32p_row04_traceSegment_077_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 0 27 27, g32p_row04_traceSegment_077_0000_0027, g32p_row04_traceSegment_077_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 54 13 14, g32p_row04_traceSegment_077_0054_0013, g32p_row04_traceSegment_077_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 81 13 14, g32p_row04_traceSegment_077_0081_0013, g32p_row04_traceSegment_077_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 54 27 27, g32p_row04_traceSegment_077_0054_0027, g32p_row04_traceSegment_077_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 0 54 54, g32p_row04_traceSegment_077_0000_0054, g32p_row04_traceSegment_077_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 108 13 14, g32p_row04_traceSegment_077_0108_0013, g32p_row04_traceSegment_077_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 135 13 14, g32p_row04_traceSegment_077_0135_0013, g32p_row04_traceSegment_077_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 108 27 27, g32p_row04_traceSegment_077_0108_0027, g32p_row04_traceSegment_077_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 162 13 14, g32p_row04_traceSegment_077_0162_0013, g32p_row04_traceSegment_077_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 189 13 14, g32p_row04_traceSegment_077_0189_0013, g32p_row04_traceSegment_077_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 162 27 27, g32p_row04_traceSegment_077_0162_0027, g32p_row04_traceSegment_077_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 108 54 54, g32p_row04_traceSegment_077_0108_0054, g32p_row04_traceSegment_077_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_077 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 0 108 108, g32p_row04_traceSegment_077_0000_0108, g32p_row04_traceSegment_077_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 216 13 14, g32p_row04_traceSegment_077_0216_0013, g32p_row04_traceSegment_077_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 243 13 14, g32p_row04_traceSegment_077_0243_0013, g32p_row04_traceSegment_077_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 216 27 27, g32p_row04_traceSegment_077_0216_0027, g32p_row04_traceSegment_077_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 270 13 14, g32p_row04_traceSegment_077_0270_0013, g32p_row04_traceSegment_077_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 297 13 14, g32p_row04_traceSegment_077_0297_0013, g32p_row04_traceSegment_077_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 270 27 27, g32p_row04_traceSegment_077_0270_0027, g32p_row04_traceSegment_077_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 216 54 54, g32p_row04_traceSegment_077_0216_0054, g32p_row04_traceSegment_077_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 324 13 14, g32p_row04_traceSegment_077_0324_0013, g32p_row04_traceSegment_077_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 351 13 14, g32p_row04_traceSegment_077_0351_0013, g32p_row04_traceSegment_077_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 324 27 27, g32p_row04_traceSegment_077_0324_0027, g32p_row04_traceSegment_077_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 378 13 14, g32p_row04_traceSegment_077_0378_0013, g32p_row04_traceSegment_077_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 405 13 14, g32p_row04_traceSegment_077_0405_0013, g32p_row04_traceSegment_077_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 378 27 27, g32p_row04_traceSegment_077_0378_0027, g32p_row04_traceSegment_077_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 324 54 54, g32p_row04_traceSegment_077_0324_0054, g32p_row04_traceSegment_077_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_077 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 216 108 108, g32p_row04_traceSegment_077_0216_0108, g32p_row04_traceSegment_077_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_077 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 0 216 216, g32p_row04_traceSegment_077_0000_0216, g32p_row04_traceSegment_077_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 432 13 14, g32p_row04_traceSegment_077_0432_0013, g32p_row04_traceSegment_077_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 459 13 14, g32p_row04_traceSegment_077_0459_0013, g32p_row04_traceSegment_077_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 432 27 27, g32p_row04_traceSegment_077_0432_0027, g32p_row04_traceSegment_077_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 486 13 14, g32p_row04_traceSegment_077_0486_0013, g32p_row04_traceSegment_077_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 513 13 14, g32p_row04_traceSegment_077_0513_0013, g32p_row04_traceSegment_077_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 486 27 27, g32p_row04_traceSegment_077_0486_0027, g32p_row04_traceSegment_077_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 432 54 54, g32p_row04_traceSegment_077_0432_0054, g32p_row04_traceSegment_077_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 540 13 14, g32p_row04_traceSegment_077_0540_0013, g32p_row04_traceSegment_077_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 567 13 14, g32p_row04_traceSegment_077_0567_0013, g32p_row04_traceSegment_077_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 540 27 27, g32p_row04_traceSegment_077_0540_0027, g32p_row04_traceSegment_077_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 594 13 14, g32p_row04_traceSegment_077_0594_0013, g32p_row04_traceSegment_077_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 621 13 14, g32p_row04_traceSegment_077_0621_0013, g32p_row04_traceSegment_077_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 594 27 27, g32p_row04_traceSegment_077_0594_0027, g32p_row04_traceSegment_077_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 540 54 54, g32p_row04_traceSegment_077_0540_0054, g32p_row04_traceSegment_077_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_077 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 432 108 108, g32p_row04_traceSegment_077_0432_0108, g32p_row04_traceSegment_077_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 648 13 14, g32p_row04_traceSegment_077_0648_0013, g32p_row04_traceSegment_077_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 675 13 14, g32p_row04_traceSegment_077_0675_0013, g32p_row04_traceSegment_077_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 648 27 27, g32p_row04_traceSegment_077_0648_0027, g32p_row04_traceSegment_077_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 702 13 14, g32p_row04_traceSegment_077_0702_0013, g32p_row04_traceSegment_077_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 729 13 14, g32p_row04_traceSegment_077_0729_0013, g32p_row04_traceSegment_077_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 702 27 27, g32p_row04_traceSegment_077_0702_0027, g32p_row04_traceSegment_077_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 648 54 54, g32p_row04_traceSegment_077_0648_0054, g32p_row04_traceSegment_077_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 756 13 14, g32p_row04_traceSegment_077_0756_0013, g32p_row04_traceSegment_077_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 783 13 14, g32p_row04_traceSegment_077_0783_0013, g32p_row04_traceSegment_077_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 756 27 27, g32p_row04_traceSegment_077_0756_0027, g32p_row04_traceSegment_077_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 810 13 14, g32p_row04_traceSegment_077_0810_0013, g32p_row04_traceSegment_077_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 837 13 14, g32p_row04_traceSegment_077_0837_0013, g32p_row04_traceSegment_077_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 810 27 27, g32p_row04_traceSegment_077_0810_0027, g32p_row04_traceSegment_077_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 756 54 54, g32p_row04_traceSegment_077_0756_0054, g32p_row04_traceSegment_077_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_077 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 648 108 108, g32p_row04_traceSegment_077_0648_0108, g32p_row04_traceSegment_077_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_077 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 432 216 216, g32p_row04_traceSegment_077_0432_0216, g32p_row04_traceSegment_077_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_077 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 0 432 432, g32p_row04_traceSegment_077_0000_0432, g32p_row04_traceSegment_077_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 864 13 14, g32p_row04_traceSegment_077_0864_0013, g32p_row04_traceSegment_077_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 891 13 14, g32p_row04_traceSegment_077_0891_0013, g32p_row04_traceSegment_077_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 864 27 27, g32p_row04_traceSegment_077_0864_0027, g32p_row04_traceSegment_077_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 918 13 14, g32p_row04_traceSegment_077_0918_0013, g32p_row04_traceSegment_077_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 945 13 14, g32p_row04_traceSegment_077_0945_0013, g32p_row04_traceSegment_077_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 918 27 27, g32p_row04_traceSegment_077_0918_0027, g32p_row04_traceSegment_077_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 864 54 54, g32p_row04_traceSegment_077_0864_0054, g32p_row04_traceSegment_077_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 972 13 14, g32p_row04_traceSegment_077_0972_0013, g32p_row04_traceSegment_077_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 999 13 14, g32p_row04_traceSegment_077_0999_0013, g32p_row04_traceSegment_077_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 972 27 27, g32p_row04_traceSegment_077_0972_0027, g32p_row04_traceSegment_077_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1026 13 14, g32p_row04_traceSegment_077_1026_0013, g32p_row04_traceSegment_077_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1053 13 14, g32p_row04_traceSegment_077_1053_0013, g32p_row04_traceSegment_077_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1026 27 27, g32p_row04_traceSegment_077_1026_0027, g32p_row04_traceSegment_077_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 972 54 54, g32p_row04_traceSegment_077_0972_0054, g32p_row04_traceSegment_077_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_077 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 864 108 108, g32p_row04_traceSegment_077_0864_0108, g32p_row04_traceSegment_077_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1080 13 14, g32p_row04_traceSegment_077_1080_0013, g32p_row04_traceSegment_077_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1107 13 14, g32p_row04_traceSegment_077_1107_0013, g32p_row04_traceSegment_077_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1080 27 27, g32p_row04_traceSegment_077_1080_0027, g32p_row04_traceSegment_077_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1134 13 14, g32p_row04_traceSegment_077_1134_0013, g32p_row04_traceSegment_077_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1161 13 14, g32p_row04_traceSegment_077_1161_0013, g32p_row04_traceSegment_077_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1134 27 27, g32p_row04_traceSegment_077_1134_0027, g32p_row04_traceSegment_077_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1080 54 54, g32p_row04_traceSegment_077_1080_0054, g32p_row04_traceSegment_077_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1188 13 14, g32p_row04_traceSegment_077_1188_0013, g32p_row04_traceSegment_077_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1215 13 14, g32p_row04_traceSegment_077_1215_0013, g32p_row04_traceSegment_077_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1188 27 27, g32p_row04_traceSegment_077_1188_0027, g32p_row04_traceSegment_077_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1242 13 14, g32p_row04_traceSegment_077_1242_0013, g32p_row04_traceSegment_077_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1269 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1269 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1269 13 14, g32p_row04_traceSegment_077_1269_0013, g32p_row04_traceSegment_077_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1242 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1242 27 27, g32p_row04_traceSegment_077_1242_0027, g32p_row04_traceSegment_077_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 1188 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1188 54 54, g32p_row04_traceSegment_077_1188_0054, g32p_row04_traceSegment_077_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_077 1080 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1080 108 108, g32p_row04_traceSegment_077_1080_0108, g32p_row04_traceSegment_077_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_077 864 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 864 216 216, g32p_row04_traceSegment_077_0864_0216, g32p_row04_traceSegment_077_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1296 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1296 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1296 13 14, g32p_row04_traceSegment_077_1296_0013, g32p_row04_traceSegment_077_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1336 14 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1323 27 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1323 13 14, g32p_row04_traceSegment_077_1323_0013, g32p_row04_traceSegment_077_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1296 54 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1296 27 27, g32p_row04_traceSegment_077_1296_0027, g32p_row04_traceSegment_077_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1350 13 14, g32p_row04_traceSegment_077_1350_0013, g32p_row04_traceSegment_077_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1377 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1377 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1377 13 14, g32p_row04_traceSegment_077_1377_0013, g32p_row04_traceSegment_077_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1350 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1350 27 27, g32p_row04_traceSegment_077_1350_0027, g32p_row04_traceSegment_077_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 1296 108 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1296 54 54, g32p_row04_traceSegment_077_1296_0054, g32p_row04_traceSegment_077_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1417 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1404 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1404 13 14, g32p_row04_traceSegment_077_1404_0013, g32p_row04_traceSegment_077_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1444 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1431 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1431 13 14, g32p_row04_traceSegment_077_1431_0013, g32p_row04_traceSegment_077_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1404 54 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1404 27 27, g32p_row04_traceSegment_077_1404_0027, g32p_row04_traceSegment_077_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1458 13 14, g32p_row04_traceSegment_077_1458_0013, g32p_row04_traceSegment_077_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1485 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1485 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1485 13 14, g32p_row04_traceSegment_077_1485_0013, g32p_row04_traceSegment_077_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1458 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1458 27 27, g32p_row04_traceSegment_077_1458_0027, g32p_row04_traceSegment_077_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 1404 108 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1404 54 54, g32p_row04_traceSegment_077_1404_0054, g32p_row04_traceSegment_077_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_077 1296 216 = [4, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1296 108 108, g32p_row04_traceSegment_077_1296_0108, g32p_row04_traceSegment_077_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1512 13 14, g32p_row04_traceSegment_077_1512_0013, g32p_row04_traceSegment_077_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1539 13 14, g32p_row04_traceSegment_077_1539_0013, g32p_row04_traceSegment_077_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1512 27 27, g32p_row04_traceSegment_077_1512_0027, g32p_row04_traceSegment_077_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1566 13 14, g32p_row04_traceSegment_077_1566_0013, g32p_row04_traceSegment_077_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1593 13 14, g32p_row04_traceSegment_077_1593_0013, g32p_row04_traceSegment_077_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1566 27 27, g32p_row04_traceSegment_077_1566_0027, g32p_row04_traceSegment_077_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1512 54 54, g32p_row04_traceSegment_077_1512_0054, g32p_row04_traceSegment_077_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1620 13 14, g32p_row04_traceSegment_077_1620_0013, g32p_row04_traceSegment_077_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1647 13 14, g32p_row04_traceSegment_077_1647_0013, g32p_row04_traceSegment_077_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1620 27 27, g32p_row04_traceSegment_077_1620_0027, g32p_row04_traceSegment_077_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1674 13 14, g32p_row04_traceSegment_077_1674_0013, g32p_row04_traceSegment_077_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_077 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_077 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_077_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_077 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1701 13 14, g32p_row04_traceSegment_077_1701_0013, g32p_row04_traceSegment_077_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_077 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1674 27 27, g32p_row04_traceSegment_077_1674_0027, g32p_row04_traceSegment_077_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_077 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1620 54 54, g32p_row04_traceSegment_077_1620_0054, g32p_row04_traceSegment_077_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_077 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1512 108 108, g32p_row04_traceSegment_077_1512_0108, g32p_row04_traceSegment_077_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_077_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_077 1296 432 = [4, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 1296 216 216, g32p_row04_traceSegment_077_1296_0216, g32p_row04_traceSegment_077_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_077 864 864 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 864 432 432, g32p_row04_traceSegment_077_0864_0432, g32p_row04_traceSegment_077_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_077_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_077 0 1728 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_077 0 864 864, g32p_row04_traceSegment_077_0000_0864, g32p_row04_traceSegment_077_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 77 = [4, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_077_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_078 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 78 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_078_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 0 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 0 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 0 13 14, g32p_row04_traceSegment_078_0000_0013, g32p_row04_traceSegment_078_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 27 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 40 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 27 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 27 13 14, g32p_row04_traceSegment_078_0027_0013, g32p_row04_traceSegment_078_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 0 54 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 0 27 27, g32p_row04_traceSegment_078_0000_0027, g32p_row04_traceSegment_078_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 54 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 67 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 54 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 54 13 14, g32p_row04_traceSegment_078_0054_0013, g32p_row04_traceSegment_078_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 81 13 14, g32p_row04_traceSegment_078_0081_0013, g32p_row04_traceSegment_078_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 54 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 54 27 27, g32p_row04_traceSegment_078_0054_0027, g32p_row04_traceSegment_078_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 0 108 = [0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 0 54 54, g32p_row04_traceSegment_078_0000_0054, g32p_row04_traceSegment_078_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 108 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 121 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 108 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 108 13 14, g32p_row04_traceSegment_078_0108_0013, g32p_row04_traceSegment_078_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 135 13 14, g32p_row04_traceSegment_078_0135_0013, g32p_row04_traceSegment_078_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 108 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 108 27 27, g32p_row04_traceSegment_078_0108_0027, g32p_row04_traceSegment_078_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 162 13 14, g32p_row04_traceSegment_078_0162_0013, g32p_row04_traceSegment_078_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 189 13 14, g32p_row04_traceSegment_078_0189_0013, g32p_row04_traceSegment_078_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 162 27 27, g32p_row04_traceSegment_078_0162_0027, g32p_row04_traceSegment_078_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 108 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 108 54 54, g32p_row04_traceSegment_078_0108_0054, g32p_row04_traceSegment_078_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_078 0 216 = [0, 2, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 0 108 108, g32p_row04_traceSegment_078_0000_0108, g32p_row04_traceSegment_078_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 216 13 14, g32p_row04_traceSegment_078_0216_0013, g32p_row04_traceSegment_078_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 243 13 14, g32p_row04_traceSegment_078_0243_0013, g32p_row04_traceSegment_078_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 216 27 27, g32p_row04_traceSegment_078_0216_0027, g32p_row04_traceSegment_078_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 270 13 14, g32p_row04_traceSegment_078_0270_0013, g32p_row04_traceSegment_078_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 297 13 14, g32p_row04_traceSegment_078_0297_0013, g32p_row04_traceSegment_078_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 270 27 27, g32p_row04_traceSegment_078_0270_0027, g32p_row04_traceSegment_078_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 216 54 54, g32p_row04_traceSegment_078_0216_0054, g32p_row04_traceSegment_078_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 324 13 14, g32p_row04_traceSegment_078_0324_0013, g32p_row04_traceSegment_078_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 351 13 14, g32p_row04_traceSegment_078_0351_0013, g32p_row04_traceSegment_078_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 324 27 27, g32p_row04_traceSegment_078_0324_0027, g32p_row04_traceSegment_078_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 378 13 14, g32p_row04_traceSegment_078_0378_0013, g32p_row04_traceSegment_078_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 418 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 405 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 405 13 14, g32p_row04_traceSegment_078_0405_0013, g32p_row04_traceSegment_078_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 378 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 378 27 27, g32p_row04_traceSegment_078_0378_0027, g32p_row04_traceSegment_078_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 324 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 324 54 54, g32p_row04_traceSegment_078_0324_0054, g32p_row04_traceSegment_078_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_078 216 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 216 108 108, g32p_row04_traceSegment_078_0216_0108, g32p_row04_traceSegment_078_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_078 0 432 = [0, 3, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 0 216 216, g32p_row04_traceSegment_078_0000_0216, g32p_row04_traceSegment_078_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 445 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 432 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 432 13 14, g32p_row04_traceSegment_078_0432_0013, g32p_row04_traceSegment_078_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 459 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 459 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 459 13 14, g32p_row04_traceSegment_078_0459_0013, g32p_row04_traceSegment_078_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 432 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 432 27 27, g32p_row04_traceSegment_078_0432_0027, g32p_row04_traceSegment_078_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 486 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 486 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 486 13 14, g32p_row04_traceSegment_078_0486_0013, g32p_row04_traceSegment_078_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 513 13 14, g32p_row04_traceSegment_078_0513_0013, g32p_row04_traceSegment_078_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 486 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 486 27 27, g32p_row04_traceSegment_078_0486_0027, g32p_row04_traceSegment_078_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 432 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 432 54 54, g32p_row04_traceSegment_078_0432_0054, g32p_row04_traceSegment_078_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 540 13 14, g32p_row04_traceSegment_078_0540_0013, g32p_row04_traceSegment_078_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 567 13 14, g32p_row04_traceSegment_078_0567_0013, g32p_row04_traceSegment_078_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 540 27 27, g32p_row04_traceSegment_078_0540_0027, g32p_row04_traceSegment_078_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 594 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 607 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 594 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 594 13 14, g32p_row04_traceSegment_078_0594_0013, g32p_row04_traceSegment_078_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 621 13 14, g32p_row04_traceSegment_078_0621_0013, g32p_row04_traceSegment_078_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 594 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 594 27 27, g32p_row04_traceSegment_078_0594_0027, g32p_row04_traceSegment_078_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 540 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 540 54 54, g32p_row04_traceSegment_078_0540_0054, g32p_row04_traceSegment_078_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_078 432 216 = [0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 432 108 108, g32p_row04_traceSegment_078_0432_0108, g32p_row04_traceSegment_078_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 648 13 14, g32p_row04_traceSegment_078_0648_0013, g32p_row04_traceSegment_078_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 675 13 14, g32p_row04_traceSegment_078_0675_0013, g32p_row04_traceSegment_078_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 648 27 27, g32p_row04_traceSegment_078_0648_0027, g32p_row04_traceSegment_078_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 702 13 14, g32p_row04_traceSegment_078_0702_0013, g32p_row04_traceSegment_078_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 729 13 14, g32p_row04_traceSegment_078_0729_0013, g32p_row04_traceSegment_078_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 702 27 27, g32p_row04_traceSegment_078_0702_0027, g32p_row04_traceSegment_078_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 648 54 54, g32p_row04_traceSegment_078_0648_0054, g32p_row04_traceSegment_078_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 756 13 14, g32p_row04_traceSegment_078_0756_0013, g32p_row04_traceSegment_078_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 783 13 14, g32p_row04_traceSegment_078_0783_0013, g32p_row04_traceSegment_078_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 756 27 27, g32p_row04_traceSegment_078_0756_0027, g32p_row04_traceSegment_078_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 810 13 14, g32p_row04_traceSegment_078_0810_0013, g32p_row04_traceSegment_078_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 837 13 14, g32p_row04_traceSegment_078_0837_0013, g32p_row04_traceSegment_078_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 810 27 27, g32p_row04_traceSegment_078_0810_0027, g32p_row04_traceSegment_078_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 756 54 54, g32p_row04_traceSegment_078_0756_0054, g32p_row04_traceSegment_078_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_078 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 648 108 108, g32p_row04_traceSegment_078_0648_0108, g32p_row04_traceSegment_078_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_078 432 432 = [0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 432 216 216, g32p_row04_traceSegment_078_0432_0216, g32p_row04_traceSegment_078_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_078 0 864 = [0, 7, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 0 432 432, g32p_row04_traceSegment_078_0000_0432, g32p_row04_traceSegment_078_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 864 13 14, g32p_row04_traceSegment_078_0864_0013, g32p_row04_traceSegment_078_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 891 13 14, g32p_row04_traceSegment_078_0891_0013, g32p_row04_traceSegment_078_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 864 27 27, g32p_row04_traceSegment_078_0864_0027, g32p_row04_traceSegment_078_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 918 13 14, g32p_row04_traceSegment_078_0918_0013, g32p_row04_traceSegment_078_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 945 13 14, g32p_row04_traceSegment_078_0945_0013, g32p_row04_traceSegment_078_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 918 27 27, g32p_row04_traceSegment_078_0918_0027, g32p_row04_traceSegment_078_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 864 54 54, g32p_row04_traceSegment_078_0864_0054, g32p_row04_traceSegment_078_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 972 13 14, g32p_row04_traceSegment_078_0972_0013, g32p_row04_traceSegment_078_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 999 13 14, g32p_row04_traceSegment_078_0999_0013, g32p_row04_traceSegment_078_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 972 27 27, g32p_row04_traceSegment_078_0972_0027, g32p_row04_traceSegment_078_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1026 13 14, g32p_row04_traceSegment_078_1026_0013, g32p_row04_traceSegment_078_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1053 13 14, g32p_row04_traceSegment_078_1053_0013, g32p_row04_traceSegment_078_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1026 27 27, g32p_row04_traceSegment_078_1026_0027, g32p_row04_traceSegment_078_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 972 54 54, g32p_row04_traceSegment_078_0972_0054, g32p_row04_traceSegment_078_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_078 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 864 108 108, g32p_row04_traceSegment_078_0864_0108, g32p_row04_traceSegment_078_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1080 13 14, g32p_row04_traceSegment_078_1080_0013, g32p_row04_traceSegment_078_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1107 13 14, g32p_row04_traceSegment_078_1107_0013, g32p_row04_traceSegment_078_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1080 27 27, g32p_row04_traceSegment_078_1080_0027, g32p_row04_traceSegment_078_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1134 13 14, g32p_row04_traceSegment_078_1134_0013, g32p_row04_traceSegment_078_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1161 13 14, g32p_row04_traceSegment_078_1161_0013, g32p_row04_traceSegment_078_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1134 27 27, g32p_row04_traceSegment_078_1134_0027, g32p_row04_traceSegment_078_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1080 54 54, g32p_row04_traceSegment_078_1080_0054, g32p_row04_traceSegment_078_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1201 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1188 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1188 13 14, g32p_row04_traceSegment_078_1188_0013, g32p_row04_traceSegment_078_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1215 13 14, g32p_row04_traceSegment_078_1215_0013, g32p_row04_traceSegment_078_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1188 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1188 27 27, g32p_row04_traceSegment_078_1188_0027, g32p_row04_traceSegment_078_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1242 13 14, g32p_row04_traceSegment_078_1242_0013, g32p_row04_traceSegment_078_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1282 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1269 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1269 13 14, g32p_row04_traceSegment_078_1269_0013, g32p_row04_traceSegment_078_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1242 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1242 27 27, g32p_row04_traceSegment_078_1242_0027, g32p_row04_traceSegment_078_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 1188 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1188 54 54, g32p_row04_traceSegment_078_1188_0054, g32p_row04_traceSegment_078_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_078 1080 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1080 108 108, g32p_row04_traceSegment_078_1080_0108, g32p_row04_traceSegment_078_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_078 864 432 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 864 216 216, g32p_row04_traceSegment_078_0864_0216, g32p_row04_traceSegment_078_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1309 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1296 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1296 13 14, g32p_row04_traceSegment_078_1296_0013, g32p_row04_traceSegment_078_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1323 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1336 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1323 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1323 13 14, g32p_row04_traceSegment_078_1323_0013, g32p_row04_traceSegment_078_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1296 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1296 27 27, g32p_row04_traceSegment_078_1296_0027, g32p_row04_traceSegment_078_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1350 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1350 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1350 13 14, g32p_row04_traceSegment_078_1350_0013, g32p_row04_traceSegment_078_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1377 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1390 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1377 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1377 13 14, g32p_row04_traceSegment_078_1377_0013, g32p_row04_traceSegment_078_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1350 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1350 27 27, g32p_row04_traceSegment_078_1350_0027, g32p_row04_traceSegment_078_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 1296 108 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1296 54 54, g32p_row04_traceSegment_078_1296_0054, g32p_row04_traceSegment_078_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1404 13 14, g32p_row04_traceSegment_078_1404_0013, g32p_row04_traceSegment_078_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1431 13 14, g32p_row04_traceSegment_078_1431_0013, g32p_row04_traceSegment_078_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1404 27 27, g32p_row04_traceSegment_078_1404_0027, g32p_row04_traceSegment_078_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1458 13 14, g32p_row04_traceSegment_078_1458_0013, g32p_row04_traceSegment_078_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1485 13 14, g32p_row04_traceSegment_078_1485_0013, g32p_row04_traceSegment_078_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1458 27 27, g32p_row04_traceSegment_078_1458_0027, g32p_row04_traceSegment_078_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1404 54 54, g32p_row04_traceSegment_078_1404_0054, g32p_row04_traceSegment_078_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_078 1296 216 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1296 108 108, g32p_row04_traceSegment_078_1296_0108, g32p_row04_traceSegment_078_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1525 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1512 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1512 13 14, g32p_row04_traceSegment_078_1512_0013, g32p_row04_traceSegment_078_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1539 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1552 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1539 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1539 13 14, g32p_row04_traceSegment_078_1539_0013, g32p_row04_traceSegment_078_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1512 54 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1512 27 27, g32p_row04_traceSegment_078_1512_0027, g32p_row04_traceSegment_078_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1566 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1566 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1566 13 14, g32p_row04_traceSegment_078_1566_0013, g32p_row04_traceSegment_078_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1593 13 14, g32p_row04_traceSegment_078_1593_0013, g32p_row04_traceSegment_078_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1566 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1566 27 27, g32p_row04_traceSegment_078_1566_0027, g32p_row04_traceSegment_078_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 1512 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1512 54 54, g32p_row04_traceSegment_078_1512_0054, g32p_row04_traceSegment_078_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1620 13 14, g32p_row04_traceSegment_078_1620_0013, g32p_row04_traceSegment_078_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1647 13 14, g32p_row04_traceSegment_078_1647_0013, g32p_row04_traceSegment_078_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1620 27 27, g32p_row04_traceSegment_078_1620_0027, g32p_row04_traceSegment_078_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1674 13 14, g32p_row04_traceSegment_078_1674_0013, g32p_row04_traceSegment_078_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_078 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_078 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_078_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_078 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1701 13 14, g32p_row04_traceSegment_078_1701_0013, g32p_row04_traceSegment_078_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_078 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1674 27 27, g32p_row04_traceSegment_078_1674_0027, g32p_row04_traceSegment_078_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_078 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1620 54 54, g32p_row04_traceSegment_078_1620_0054, g32p_row04_traceSegment_078_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_078 1512 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1512 108 108, g32p_row04_traceSegment_078_1512_0108, g32p_row04_traceSegment_078_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_078_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_078 1296 432 = [0, 6, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 1296 216 216, g32p_row04_traceSegment_078_1296_0216, g32p_row04_traceSegment_078_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_078 864 864 = [0, 9, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 864 432 432, g32p_row04_traceSegment_078_0864_0432, g32p_row04_traceSegment_078_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_078_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_078 0 1728 = [0, 16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_078 0 864 864, g32p_row04_traceSegment_078_0000_0864, g32p_row04_traceSegment_078_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 78 = [0, 16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_078_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_079 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 79 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_079_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 0 13 14, g32p_row04_traceSegment_079_0000_0013, g32p_row04_traceSegment_079_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 27 13 14, g32p_row04_traceSegment_079_0027_0013, g32p_row04_traceSegment_079_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 0 27 27, g32p_row04_traceSegment_079_0000_0027, g32p_row04_traceSegment_079_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 54 13 14, g32p_row04_traceSegment_079_0054_0013, g32p_row04_traceSegment_079_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 81 13 14, g32p_row04_traceSegment_079_0081_0013, g32p_row04_traceSegment_079_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 54 27 27, g32p_row04_traceSegment_079_0054_0027, g32p_row04_traceSegment_079_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 0 54 54, g32p_row04_traceSegment_079_0000_0054, g32p_row04_traceSegment_079_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 108 13 14, g32p_row04_traceSegment_079_0108_0013, g32p_row04_traceSegment_079_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 135 13 14, g32p_row04_traceSegment_079_0135_0013, g32p_row04_traceSegment_079_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 108 27 27, g32p_row04_traceSegment_079_0108_0027, g32p_row04_traceSegment_079_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 162 13 14, g32p_row04_traceSegment_079_0162_0013, g32p_row04_traceSegment_079_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 189 13 14, g32p_row04_traceSegment_079_0189_0013, g32p_row04_traceSegment_079_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 162 27 27, g32p_row04_traceSegment_079_0162_0027, g32p_row04_traceSegment_079_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 108 54 54, g32p_row04_traceSegment_079_0108_0054, g32p_row04_traceSegment_079_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_079 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 0 108 108, g32p_row04_traceSegment_079_0000_0108, g32p_row04_traceSegment_079_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 216 13 14, g32p_row04_traceSegment_079_0216_0013, g32p_row04_traceSegment_079_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 243 13 14, g32p_row04_traceSegment_079_0243_0013, g32p_row04_traceSegment_079_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 216 27 27, g32p_row04_traceSegment_079_0216_0027, g32p_row04_traceSegment_079_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 270 13 14, g32p_row04_traceSegment_079_0270_0013, g32p_row04_traceSegment_079_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 297 13 14, g32p_row04_traceSegment_079_0297_0013, g32p_row04_traceSegment_079_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 270 27 27, g32p_row04_traceSegment_079_0270_0027, g32p_row04_traceSegment_079_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 216 54 54, g32p_row04_traceSegment_079_0216_0054, g32p_row04_traceSegment_079_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 324 13 14, g32p_row04_traceSegment_079_0324_0013, g32p_row04_traceSegment_079_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 351 13 14, g32p_row04_traceSegment_079_0351_0013, g32p_row04_traceSegment_079_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 324 27 27, g32p_row04_traceSegment_079_0324_0027, g32p_row04_traceSegment_079_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 378 13 14, g32p_row04_traceSegment_079_0378_0013, g32p_row04_traceSegment_079_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 405 13 14, g32p_row04_traceSegment_079_0405_0013, g32p_row04_traceSegment_079_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 378 27 27, g32p_row04_traceSegment_079_0378_0027, g32p_row04_traceSegment_079_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 324 54 54, g32p_row04_traceSegment_079_0324_0054, g32p_row04_traceSegment_079_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_079 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 216 108 108, g32p_row04_traceSegment_079_0216_0108, g32p_row04_traceSegment_079_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_079 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 0 216 216, g32p_row04_traceSegment_079_0000_0216, g32p_row04_traceSegment_079_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 432 13 14, g32p_row04_traceSegment_079_0432_0013, g32p_row04_traceSegment_079_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 459 13 14, g32p_row04_traceSegment_079_0459_0013, g32p_row04_traceSegment_079_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 432 27 27, g32p_row04_traceSegment_079_0432_0027, g32p_row04_traceSegment_079_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 486 13 14, g32p_row04_traceSegment_079_0486_0013, g32p_row04_traceSegment_079_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 513 13 14, g32p_row04_traceSegment_079_0513_0013, g32p_row04_traceSegment_079_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 486 27 27, g32p_row04_traceSegment_079_0486_0027, g32p_row04_traceSegment_079_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 432 54 54, g32p_row04_traceSegment_079_0432_0054, g32p_row04_traceSegment_079_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 540 13 14, g32p_row04_traceSegment_079_0540_0013, g32p_row04_traceSegment_079_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 567 13 14, g32p_row04_traceSegment_079_0567_0013, g32p_row04_traceSegment_079_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 540 27 27, g32p_row04_traceSegment_079_0540_0027, g32p_row04_traceSegment_079_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 594 13 14, g32p_row04_traceSegment_079_0594_0013, g32p_row04_traceSegment_079_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 634 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 621 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 621 13 14, g32p_row04_traceSegment_079_0621_0013, g32p_row04_traceSegment_079_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 594 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 594 27 27, g32p_row04_traceSegment_079_0594_0027, g32p_row04_traceSegment_079_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 540 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 540 54 54, g32p_row04_traceSegment_079_0540_0054, g32p_row04_traceSegment_079_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_079 432 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 432 108 108, g32p_row04_traceSegment_079_0432_0108, g32p_row04_traceSegment_079_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 648 13 14, g32p_row04_traceSegment_079_0648_0013, g32p_row04_traceSegment_079_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 675 13 14, g32p_row04_traceSegment_079_0675_0013, g32p_row04_traceSegment_079_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 648 27 27, g32p_row04_traceSegment_079_0648_0027, g32p_row04_traceSegment_079_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 702 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 702 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 702 13 14, g32p_row04_traceSegment_079_0702_0013, g32p_row04_traceSegment_079_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 729 13 14, g32p_row04_traceSegment_079_0729_0013, g32p_row04_traceSegment_079_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 702 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 702 27 27, g32p_row04_traceSegment_079_0702_0027, g32p_row04_traceSegment_079_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 648 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 648 54 54, g32p_row04_traceSegment_079_0648_0054, g32p_row04_traceSegment_079_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 756 13 14, g32p_row04_traceSegment_079_0756_0013, g32p_row04_traceSegment_079_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 783 13 14, g32p_row04_traceSegment_079_0783_0013, g32p_row04_traceSegment_079_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 756 27 27, g32p_row04_traceSegment_079_0756_0027, g32p_row04_traceSegment_079_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 810 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 810 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 810 13 14, g32p_row04_traceSegment_079_0810_0013, g32p_row04_traceSegment_079_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 837 13 14, g32p_row04_traceSegment_079_0837_0013, g32p_row04_traceSegment_079_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 810 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 810 27 27, g32p_row04_traceSegment_079_0810_0027, g32p_row04_traceSegment_079_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 756 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 756 54 54, g32p_row04_traceSegment_079_0756_0054, g32p_row04_traceSegment_079_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_079 648 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 648 108 108, g32p_row04_traceSegment_079_0648_0108, g32p_row04_traceSegment_079_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_079 432 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 432 216 216, g32p_row04_traceSegment_079_0432_0216, g32p_row04_traceSegment_079_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_079 0 864 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 0 432 432, g32p_row04_traceSegment_079_0000_0432, g32p_row04_traceSegment_079_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 864 13 14, g32p_row04_traceSegment_079_0864_0013, g32p_row04_traceSegment_079_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 891 13 14, g32p_row04_traceSegment_079_0891_0013, g32p_row04_traceSegment_079_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 864 27 27, g32p_row04_traceSegment_079_0864_0027, g32p_row04_traceSegment_079_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 918 13 14, g32p_row04_traceSegment_079_0918_0013, g32p_row04_traceSegment_079_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 945 13 14, g32p_row04_traceSegment_079_0945_0013, g32p_row04_traceSegment_079_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 918 27 27, g32p_row04_traceSegment_079_0918_0027, g32p_row04_traceSegment_079_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 864 54 54, g32p_row04_traceSegment_079_0864_0054, g32p_row04_traceSegment_079_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 972 13 14, g32p_row04_traceSegment_079_0972_0013, g32p_row04_traceSegment_079_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 999 13 14, g32p_row04_traceSegment_079_0999_0013, g32p_row04_traceSegment_079_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 972 27 27, g32p_row04_traceSegment_079_0972_0027, g32p_row04_traceSegment_079_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1026 13 14, g32p_row04_traceSegment_079_1026_0013, g32p_row04_traceSegment_079_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1053 13 14, g32p_row04_traceSegment_079_1053_0013, g32p_row04_traceSegment_079_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1026 27 27, g32p_row04_traceSegment_079_1026_0027, g32p_row04_traceSegment_079_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 972 54 54, g32p_row04_traceSegment_079_0972_0054, g32p_row04_traceSegment_079_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_079 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 864 108 108, g32p_row04_traceSegment_079_0864_0108, g32p_row04_traceSegment_079_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1080 13 14, g32p_row04_traceSegment_079_1080_0013, g32p_row04_traceSegment_079_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1107 13 14, g32p_row04_traceSegment_079_1107_0013, g32p_row04_traceSegment_079_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1080 27 27, g32p_row04_traceSegment_079_1080_0027, g32p_row04_traceSegment_079_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1134 13 14, g32p_row04_traceSegment_079_1134_0013, g32p_row04_traceSegment_079_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1161 13 14, g32p_row04_traceSegment_079_1161_0013, g32p_row04_traceSegment_079_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1134 27 27, g32p_row04_traceSegment_079_1134_0027, g32p_row04_traceSegment_079_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1080 54 54, g32p_row04_traceSegment_079_1080_0054, g32p_row04_traceSegment_079_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1188 13 14, g32p_row04_traceSegment_079_1188_0013, g32p_row04_traceSegment_079_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1215 13 14, g32p_row04_traceSegment_079_1215_0013, g32p_row04_traceSegment_079_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1188 27 27, g32p_row04_traceSegment_079_1188_0027, g32p_row04_traceSegment_079_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1242 13 14, g32p_row04_traceSegment_079_1242_0013, g32p_row04_traceSegment_079_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1269 13 14, g32p_row04_traceSegment_079_1269_0013, g32p_row04_traceSegment_079_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1242 27 27, g32p_row04_traceSegment_079_1242_0027, g32p_row04_traceSegment_079_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1188 54 54, g32p_row04_traceSegment_079_1188_0054, g32p_row04_traceSegment_079_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_079 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1080 108 108, g32p_row04_traceSegment_079_1080_0108, g32p_row04_traceSegment_079_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_079 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 864 216 216, g32p_row04_traceSegment_079_0864_0216, g32p_row04_traceSegment_079_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1296 13 14, g32p_row04_traceSegment_079_1296_0013, g32p_row04_traceSegment_079_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1323 13 14, g32p_row04_traceSegment_079_1323_0013, g32p_row04_traceSegment_079_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1296 27 27, g32p_row04_traceSegment_079_1296_0027, g32p_row04_traceSegment_079_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1350 13 14, g32p_row04_traceSegment_079_1350_0013, g32p_row04_traceSegment_079_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1377 13 14, g32p_row04_traceSegment_079_1377_0013, g32p_row04_traceSegment_079_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1350 27 27, g32p_row04_traceSegment_079_1350_0027, g32p_row04_traceSegment_079_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1296 54 54, g32p_row04_traceSegment_079_1296_0054, g32p_row04_traceSegment_079_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1404 13 14, g32p_row04_traceSegment_079_1404_0013, g32p_row04_traceSegment_079_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1431 13 14, g32p_row04_traceSegment_079_1431_0013, g32p_row04_traceSegment_079_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1404 27 27, g32p_row04_traceSegment_079_1404_0027, g32p_row04_traceSegment_079_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1458 13 14, g32p_row04_traceSegment_079_1458_0013, g32p_row04_traceSegment_079_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1485 13 14, g32p_row04_traceSegment_079_1485_0013, g32p_row04_traceSegment_079_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1458 27 27, g32p_row04_traceSegment_079_1458_0027, g32p_row04_traceSegment_079_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1404 54 54, g32p_row04_traceSegment_079_1404_0054, g32p_row04_traceSegment_079_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_079 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1296 108 108, g32p_row04_traceSegment_079_1296_0108, g32p_row04_traceSegment_079_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1512 13 14, g32p_row04_traceSegment_079_1512_0013, g32p_row04_traceSegment_079_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1539 13 14, g32p_row04_traceSegment_079_1539_0013, g32p_row04_traceSegment_079_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1512 27 27, g32p_row04_traceSegment_079_1512_0027, g32p_row04_traceSegment_079_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1566 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1579 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1566 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1566 13 14, g32p_row04_traceSegment_079_1566_0013, g32p_row04_traceSegment_079_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1606 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1593 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1593 13 14, g32p_row04_traceSegment_079_1593_0013, g32p_row04_traceSegment_079_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1566 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1566 27 27, g32p_row04_traceSegment_079_1566_0027, g32p_row04_traceSegment_079_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 1512 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1512 54 54, g32p_row04_traceSegment_079_1512_0054, g32p_row04_traceSegment_079_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1620 13 14, g32p_row04_traceSegment_079_1620_0013, g32p_row04_traceSegment_079_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1647 13 14, g32p_row04_traceSegment_079_1647_0013, g32p_row04_traceSegment_079_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1620 27 27, g32p_row04_traceSegment_079_1620_0027, g32p_row04_traceSegment_079_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1674 13 14, g32p_row04_traceSegment_079_1674_0013, g32p_row04_traceSegment_079_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_079 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_079 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_079_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_079 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1701 13 14, g32p_row04_traceSegment_079_1701_0013, g32p_row04_traceSegment_079_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_079 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1674 27 27, g32p_row04_traceSegment_079_1674_0027, g32p_row04_traceSegment_079_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_079 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1620 54 54, g32p_row04_traceSegment_079_1620_0054, g32p_row04_traceSegment_079_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_079 1512 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1512 108 108, g32p_row04_traceSegment_079_1512_0108, g32p_row04_traceSegment_079_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_079_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_079 1296 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 1296 216 216, g32p_row04_traceSegment_079_1296_0216, g32p_row04_traceSegment_079_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_079 864 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 864 432 432, g32p_row04_traceSegment_079_0864_0432, g32p_row04_traceSegment_079_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_079_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_079 0 1728 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_079 0 864 864, g32p_row04_traceSegment_079_0000_0864, g32p_row04_traceSegment_079_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 79 = [4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_079_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 71) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 71) (g32p_literalTraceValue 3 71)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_071]
  decide +kernel

theorem g32p_row04_tracePolynomial_072 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 72) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 72) (g32p_literalTraceValue 3 72)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_072]
  decide +kernel

theorem g32p_row04_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 74) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 74) (g32p_literalTraceValue 3 74)
      [1, 1, 1] [3456] = true := by
  rw [g32p_row04_traceCoefficients_074]
  decide +kernel

theorem g32p_row04_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 75) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 75) (g32p_literalTraceValue 3 75)
      [1, 1, 1] [5184] = true := by
  rw [g32p_row04_traceCoefficients_075]
  decide +kernel

theorem g32p_row04_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 76) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 76) (g32p_literalTraceValue 3 76)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row04_traceCoefficients_076]
  decide +kernel

theorem g32p_row04_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 77) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 77) (g32p_literalTraceValue 3 77)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_077]
  decide +kernel

theorem g32p_row04_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 78) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 78) (g32p_literalTraceValue 3 78)
      [1, 1, 1] [10368] = true := by
  rw [g32p_row04_traceCoefficients_078]
  decide +kernel

theorem g32p_row04_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 79) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 79) (g32p_literalTraceValue 3 79)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_079]
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_080 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 80 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_080_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 0 13 14, g32p_row04_traceSegment_080_0000_0013, g32p_row04_traceSegment_080_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 27 13 14, g32p_row04_traceSegment_080_0027_0013, g32p_row04_traceSegment_080_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 0 27 27, g32p_row04_traceSegment_080_0000_0027, g32p_row04_traceSegment_080_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 54 13 14, g32p_row04_traceSegment_080_0054_0013, g32p_row04_traceSegment_080_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 81 13 14, g32p_row04_traceSegment_080_0081_0013, g32p_row04_traceSegment_080_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 54 27 27, g32p_row04_traceSegment_080_0054_0027, g32p_row04_traceSegment_080_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 0 54 54, g32p_row04_traceSegment_080_0000_0054, g32p_row04_traceSegment_080_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 108 13 14, g32p_row04_traceSegment_080_0108_0013, g32p_row04_traceSegment_080_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 135 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 148 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 135 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 135 13 14, g32p_row04_traceSegment_080_0135_0013, g32p_row04_traceSegment_080_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 108 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 108 27 27, g32p_row04_traceSegment_080_0108_0027, g32p_row04_traceSegment_080_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 162 13 = [1, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 175 14 = [1, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 162 27 = [2, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 162 13 14, g32p_row04_traceSegment_080_0162_0013, g32p_row04_traceSegment_080_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 189 13 = [2, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 202 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 189 27 = [4, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 189 13 14, g32p_row04_traceSegment_080_0189_0013, g32p_row04_traceSegment_080_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 162 54 = [6, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 162 27 27, g32p_row04_traceSegment_080_0162_0027, g32p_row04_traceSegment_080_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 108 108 = [6, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 108 54 54, g32p_row04_traceSegment_080_0108_0054, g32p_row04_traceSegment_080_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_080 0 216 = [6, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 0 108 108, g32p_row04_traceSegment_080_0000_0108, g32p_row04_traceSegment_080_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 216 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 229 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 216 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 216 13 14, g32p_row04_traceSegment_080_0216_0013, g32p_row04_traceSegment_080_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 243 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 256 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 243 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 243 13 14, g32p_row04_traceSegment_080_0243_0013, g32p_row04_traceSegment_080_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 216 54 = [10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 216 27 27, g32p_row04_traceSegment_080_0216_0027, g32p_row04_traceSegment_080_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 270 13 14, g32p_row04_traceSegment_080_0270_0013, g32p_row04_traceSegment_080_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 297 13 14, g32p_row04_traceSegment_080_0297_0013, g32p_row04_traceSegment_080_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 270 27 27, g32p_row04_traceSegment_080_0270_0027, g32p_row04_traceSegment_080_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 216 108 = [10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 216 54 54, g32p_row04_traceSegment_080_0216_0054, g32p_row04_traceSegment_080_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 324 13 14, g32p_row04_traceSegment_080_0324_0013, g32p_row04_traceSegment_080_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 351 13 14, g32p_row04_traceSegment_080_0351_0013, g32p_row04_traceSegment_080_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 324 27 27, g32p_row04_traceSegment_080_0324_0027, g32p_row04_traceSegment_080_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 378 13 14, g32p_row04_traceSegment_080_0378_0013, g32p_row04_traceSegment_080_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 405 13 14, g32p_row04_traceSegment_080_0405_0013, g32p_row04_traceSegment_080_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 378 27 27, g32p_row04_traceSegment_080_0378_0027, g32p_row04_traceSegment_080_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 324 54 54, g32p_row04_traceSegment_080_0324_0054, g32p_row04_traceSegment_080_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_080 216 216 = [10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 216 108 108, g32p_row04_traceSegment_080_0216_0108, g32p_row04_traceSegment_080_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_080 0 432 = [16, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 0 216 216, g32p_row04_traceSegment_080_0000_0216, g32p_row04_traceSegment_080_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 432 13 14, g32p_row04_traceSegment_080_0432_0013, g32p_row04_traceSegment_080_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 459 13 14, g32p_row04_traceSegment_080_0459_0013, g32p_row04_traceSegment_080_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 432 27 27, g32p_row04_traceSegment_080_0432_0027, g32p_row04_traceSegment_080_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 486 13 14, g32p_row04_traceSegment_080_0486_0013, g32p_row04_traceSegment_080_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 513 13 14, g32p_row04_traceSegment_080_0513_0013, g32p_row04_traceSegment_080_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 486 27 27, g32p_row04_traceSegment_080_0486_0027, g32p_row04_traceSegment_080_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 432 54 54, g32p_row04_traceSegment_080_0432_0054, g32p_row04_traceSegment_080_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 540 13 14, g32p_row04_traceSegment_080_0540_0013, g32p_row04_traceSegment_080_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 567 13 14, g32p_row04_traceSegment_080_0567_0013, g32p_row04_traceSegment_080_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 540 27 27, g32p_row04_traceSegment_080_0540_0027, g32p_row04_traceSegment_080_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 594 13 14, g32p_row04_traceSegment_080_0594_0013, g32p_row04_traceSegment_080_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 621 13 14, g32p_row04_traceSegment_080_0621_0013, g32p_row04_traceSegment_080_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 594 27 27, g32p_row04_traceSegment_080_0594_0027, g32p_row04_traceSegment_080_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 540 54 54, g32p_row04_traceSegment_080_0540_0054, g32p_row04_traceSegment_080_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_080 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 432 108 108, g32p_row04_traceSegment_080_0432_0108, g32p_row04_traceSegment_080_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 648 13 14, g32p_row04_traceSegment_080_0648_0013, g32p_row04_traceSegment_080_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 675 13 14, g32p_row04_traceSegment_080_0675_0013, g32p_row04_traceSegment_080_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 648 27 27, g32p_row04_traceSegment_080_0648_0027, g32p_row04_traceSegment_080_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 702 13 14, g32p_row04_traceSegment_080_0702_0013, g32p_row04_traceSegment_080_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 729 13 14, g32p_row04_traceSegment_080_0729_0013, g32p_row04_traceSegment_080_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 702 27 27, g32p_row04_traceSegment_080_0702_0027, g32p_row04_traceSegment_080_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 648 54 54, g32p_row04_traceSegment_080_0648_0054, g32p_row04_traceSegment_080_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 756 13 14, g32p_row04_traceSegment_080_0756_0013, g32p_row04_traceSegment_080_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 783 13 14, g32p_row04_traceSegment_080_0783_0013, g32p_row04_traceSegment_080_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 756 27 27, g32p_row04_traceSegment_080_0756_0027, g32p_row04_traceSegment_080_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 810 13 14, g32p_row04_traceSegment_080_0810_0013, g32p_row04_traceSegment_080_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 837 13 14, g32p_row04_traceSegment_080_0837_0013, g32p_row04_traceSegment_080_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 810 27 27, g32p_row04_traceSegment_080_0810_0027, g32p_row04_traceSegment_080_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 756 54 54, g32p_row04_traceSegment_080_0756_0054, g32p_row04_traceSegment_080_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_080 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 648 108 108, g32p_row04_traceSegment_080_0648_0108, g32p_row04_traceSegment_080_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_080 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 432 216 216, g32p_row04_traceSegment_080_0432_0216, g32p_row04_traceSegment_080_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_080 0 864 = [16, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 0 432 432, g32p_row04_traceSegment_080_0000_0432, g32p_row04_traceSegment_080_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 864 13 14, g32p_row04_traceSegment_080_0864_0013, g32p_row04_traceSegment_080_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 891 13 14, g32p_row04_traceSegment_080_0891_0013, g32p_row04_traceSegment_080_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 864 27 27, g32p_row04_traceSegment_080_0864_0027, g32p_row04_traceSegment_080_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 931 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 918 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 918 13 14, g32p_row04_traceSegment_080_0918_0013, g32p_row04_traceSegment_080_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 958 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 945 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 945 13 14, g32p_row04_traceSegment_080_0945_0013, g32p_row04_traceSegment_080_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 918 54 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 918 27 27, g32p_row04_traceSegment_080_0918_0027, g32p_row04_traceSegment_080_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 864 108 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 864 54 54, g32p_row04_traceSegment_080_0864_0054, g32p_row04_traceSegment_080_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 972 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 972 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 972 13 14, g32p_row04_traceSegment_080_0972_0013, g32p_row04_traceSegment_080_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 999 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 999 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 999 13 14, g32p_row04_traceSegment_080_0999_0013, g32p_row04_traceSegment_080_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 972 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 972 27 27, g32p_row04_traceSegment_080_0972_0027, g32p_row04_traceSegment_080_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1026 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1026 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1026 13 14, g32p_row04_traceSegment_080_1026_0013, g32p_row04_traceSegment_080_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1066 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1053 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1053 13 14, g32p_row04_traceSegment_080_1053_0013, g32p_row04_traceSegment_080_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1026 54 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1026 27 27, g32p_row04_traceSegment_080_1026_0027, g32p_row04_traceSegment_080_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 972 108 = [1, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 972 54 54, g32p_row04_traceSegment_080_0972_0054, g32p_row04_traceSegment_080_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_080 864 216 = [2, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 864 108 108, g32p_row04_traceSegment_080_0864_0108, g32p_row04_traceSegment_080_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1080 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1080 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1080 13 14, g32p_row04_traceSegment_080_1080_0013, g32p_row04_traceSegment_080_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1107 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1120 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1107 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1107 13 14, g32p_row04_traceSegment_080_1107_0013, g32p_row04_traceSegment_080_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1080 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1080 27 27, g32p_row04_traceSegment_080_1080_0027, g32p_row04_traceSegment_080_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1134 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1147 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1134 27 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1134 13 14, g32p_row04_traceSegment_080_1134_0013, g32p_row04_traceSegment_080_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1161 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1174 14 = [2, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1161 27 = [3, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1161 13 14, g32p_row04_traceSegment_080_1161_0013, g32p_row04_traceSegment_080_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1134 54 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1134 27 27, g32p_row04_traceSegment_080_1134_0027, g32p_row04_traceSegment_080_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 1080 108 = [4, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1080 54 54, g32p_row04_traceSegment_080_1080_0054, g32p_row04_traceSegment_080_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1188 13 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1201 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1188 27 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1188 13 14, g32p_row04_traceSegment_080_1188_0013, g32p_row04_traceSegment_080_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1215 13 14, g32p_row04_traceSegment_080_1215_0013, g32p_row04_traceSegment_080_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1188 54 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1188 27 27, g32p_row04_traceSegment_080_1188_0027, g32p_row04_traceSegment_080_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1242 13 14, g32p_row04_traceSegment_080_1242_0013, g32p_row04_traceSegment_080_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1269 13 14, g32p_row04_traceSegment_080_1269_0013, g32p_row04_traceSegment_080_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1242 27 27, g32p_row04_traceSegment_080_1242_0027, g32p_row04_traceSegment_080_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 1188 108 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1188 54 54, g32p_row04_traceSegment_080_1188_0054, g32p_row04_traceSegment_080_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_080 1080 216 = [6, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1080 108 108, g32p_row04_traceSegment_080_1080_0108, g32p_row04_traceSegment_080_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_080 864 432 = [8, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 864 216 216, g32p_row04_traceSegment_080_0864_0216, g32p_row04_traceSegment_080_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1296 13 14, g32p_row04_traceSegment_080_1296_0013, g32p_row04_traceSegment_080_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1323 13 14, g32p_row04_traceSegment_080_1323_0013, g32p_row04_traceSegment_080_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1296 27 27, g32p_row04_traceSegment_080_1296_0027, g32p_row04_traceSegment_080_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1350 13 14, g32p_row04_traceSegment_080_1350_0013, g32p_row04_traceSegment_080_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1377 13 14, g32p_row04_traceSegment_080_1377_0013, g32p_row04_traceSegment_080_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1350 27 27, g32p_row04_traceSegment_080_1350_0027, g32p_row04_traceSegment_080_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1296 54 54, g32p_row04_traceSegment_080_1296_0054, g32p_row04_traceSegment_080_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1404 13 14, g32p_row04_traceSegment_080_1404_0013, g32p_row04_traceSegment_080_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1431 13 14, g32p_row04_traceSegment_080_1431_0013, g32p_row04_traceSegment_080_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1404 27 27, g32p_row04_traceSegment_080_1404_0027, g32p_row04_traceSegment_080_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1458 13 14, g32p_row04_traceSegment_080_1458_0013, g32p_row04_traceSegment_080_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1485 13 14, g32p_row04_traceSegment_080_1485_0013, g32p_row04_traceSegment_080_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1458 27 27, g32p_row04_traceSegment_080_1458_0027, g32p_row04_traceSegment_080_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1404 54 54, g32p_row04_traceSegment_080_1404_0054, g32p_row04_traceSegment_080_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_080 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1296 108 108, g32p_row04_traceSegment_080_1296_0108, g32p_row04_traceSegment_080_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1512 13 14, g32p_row04_traceSegment_080_1512_0013, g32p_row04_traceSegment_080_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1539 13 14, g32p_row04_traceSegment_080_1539_0013, g32p_row04_traceSegment_080_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1512 27 27, g32p_row04_traceSegment_080_1512_0027, g32p_row04_traceSegment_080_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1566 13 14, g32p_row04_traceSegment_080_1566_0013, g32p_row04_traceSegment_080_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1593 13 14, g32p_row04_traceSegment_080_1593_0013, g32p_row04_traceSegment_080_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1566 27 27, g32p_row04_traceSegment_080_1566_0027, g32p_row04_traceSegment_080_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1512 54 54, g32p_row04_traceSegment_080_1512_0054, g32p_row04_traceSegment_080_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1620 13 14, g32p_row04_traceSegment_080_1620_0013, g32p_row04_traceSegment_080_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1647 13 14, g32p_row04_traceSegment_080_1647_0013, g32p_row04_traceSegment_080_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1620 27 27, g32p_row04_traceSegment_080_1620_0027, g32p_row04_traceSegment_080_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1674 13 14, g32p_row04_traceSegment_080_1674_0013, g32p_row04_traceSegment_080_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_080 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_080 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_080_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_080 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1701 13 14, g32p_row04_traceSegment_080_1701_0013, g32p_row04_traceSegment_080_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_080 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1674 27 27, g32p_row04_traceSegment_080_1674_0027, g32p_row04_traceSegment_080_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_080 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1620 54 54, g32p_row04_traceSegment_080_1620_0054, g32p_row04_traceSegment_080_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_080 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1512 108 108, g32p_row04_traceSegment_080_1512_0108, g32p_row04_traceSegment_080_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_080_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_080 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 1296 216 216, g32p_row04_traceSegment_080_1296_0216, g32p_row04_traceSegment_080_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_080 864 864 = [8, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 864 432 432, g32p_row04_traceSegment_080_0864_0432, g32p_row04_traceSegment_080_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_080_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_080 0 1728 = [24, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_080 0 864 864, g32p_row04_traceSegment_080_0000_0864, g32p_row04_traceSegment_080_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_080 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 80 = [24, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_080_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_081 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 81 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_081_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 0 13 14, g32p_row04_traceSegment_081_0000_0013, g32p_row04_traceSegment_081_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 27 13 14, g32p_row04_traceSegment_081_0027_0013, g32p_row04_traceSegment_081_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 0 27 27, g32p_row04_traceSegment_081_0000_0027, g32p_row04_traceSegment_081_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 54 13 14, g32p_row04_traceSegment_081_0054_0013, g32p_row04_traceSegment_081_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 81 13 14, g32p_row04_traceSegment_081_0081_0013, g32p_row04_traceSegment_081_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 54 27 27, g32p_row04_traceSegment_081_0054_0027, g32p_row04_traceSegment_081_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 0 54 54, g32p_row04_traceSegment_081_0000_0054, g32p_row04_traceSegment_081_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 108 13 14, g32p_row04_traceSegment_081_0108_0013, g32p_row04_traceSegment_081_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 135 13 14, g32p_row04_traceSegment_081_0135_0013, g32p_row04_traceSegment_081_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 108 27 27, g32p_row04_traceSegment_081_0108_0027, g32p_row04_traceSegment_081_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 175 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 162 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 162 13 14, g32p_row04_traceSegment_081_0162_0013, g32p_row04_traceSegment_081_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 202 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 189 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 189 13 14, g32p_row04_traceSegment_081_0189_0013, g32p_row04_traceSegment_081_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 162 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 162 27 27, g32p_row04_traceSegment_081_0162_0027, g32p_row04_traceSegment_081_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 108 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 108 54 54, g32p_row04_traceSegment_081_0108_0054, g32p_row04_traceSegment_081_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_081 0 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 0 108 108, g32p_row04_traceSegment_081_0000_0108, g32p_row04_traceSegment_081_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 229 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 216 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 216 13 14, g32p_row04_traceSegment_081_0216_0013, g32p_row04_traceSegment_081_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 243 13 14, g32p_row04_traceSegment_081_0243_0013, g32p_row04_traceSegment_081_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 216 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 216 27 27, g32p_row04_traceSegment_081_0216_0027, g32p_row04_traceSegment_081_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 270 13 14, g32p_row04_traceSegment_081_0270_0013, g32p_row04_traceSegment_081_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 297 13 14, g32p_row04_traceSegment_081_0297_0013, g32p_row04_traceSegment_081_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 270 27 27, g32p_row04_traceSegment_081_0270_0027, g32p_row04_traceSegment_081_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 216 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 216 54 54, g32p_row04_traceSegment_081_0216_0054, g32p_row04_traceSegment_081_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 324 13 14, g32p_row04_traceSegment_081_0324_0013, g32p_row04_traceSegment_081_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 351 13 14, g32p_row04_traceSegment_081_0351_0013, g32p_row04_traceSegment_081_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 324 27 27, g32p_row04_traceSegment_081_0324_0027, g32p_row04_traceSegment_081_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 378 13 14, g32p_row04_traceSegment_081_0378_0013, g32p_row04_traceSegment_081_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 405 13 14, g32p_row04_traceSegment_081_0405_0013, g32p_row04_traceSegment_081_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 378 27 27, g32p_row04_traceSegment_081_0378_0027, g32p_row04_traceSegment_081_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 324 54 54, g32p_row04_traceSegment_081_0324_0054, g32p_row04_traceSegment_081_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_081 216 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 216 108 108, g32p_row04_traceSegment_081_0216_0108, g32p_row04_traceSegment_081_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_081 0 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 0 216 216, g32p_row04_traceSegment_081_0000_0216, g32p_row04_traceSegment_081_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 432 13 14, g32p_row04_traceSegment_081_0432_0013, g32p_row04_traceSegment_081_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 459 13 14, g32p_row04_traceSegment_081_0459_0013, g32p_row04_traceSegment_081_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 432 27 27, g32p_row04_traceSegment_081_0432_0027, g32p_row04_traceSegment_081_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 486 13 14, g32p_row04_traceSegment_081_0486_0013, g32p_row04_traceSegment_081_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 513 13 14, g32p_row04_traceSegment_081_0513_0013, g32p_row04_traceSegment_081_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 486 27 27, g32p_row04_traceSegment_081_0486_0027, g32p_row04_traceSegment_081_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 432 54 54, g32p_row04_traceSegment_081_0432_0054, g32p_row04_traceSegment_081_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 540 13 14, g32p_row04_traceSegment_081_0540_0013, g32p_row04_traceSegment_081_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 567 13 14, g32p_row04_traceSegment_081_0567_0013, g32p_row04_traceSegment_081_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 540 27 27, g32p_row04_traceSegment_081_0540_0027, g32p_row04_traceSegment_081_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 594 13 14, g32p_row04_traceSegment_081_0594_0013, g32p_row04_traceSegment_081_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 621 13 14, g32p_row04_traceSegment_081_0621_0013, g32p_row04_traceSegment_081_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 594 27 27, g32p_row04_traceSegment_081_0594_0027, g32p_row04_traceSegment_081_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 540 54 54, g32p_row04_traceSegment_081_0540_0054, g32p_row04_traceSegment_081_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_081 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 432 108 108, g32p_row04_traceSegment_081_0432_0108, g32p_row04_traceSegment_081_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 648 13 14, g32p_row04_traceSegment_081_0648_0013, g32p_row04_traceSegment_081_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 675 13 14, g32p_row04_traceSegment_081_0675_0013, g32p_row04_traceSegment_081_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 648 27 27, g32p_row04_traceSegment_081_0648_0027, g32p_row04_traceSegment_081_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 702 13 14, g32p_row04_traceSegment_081_0702_0013, g32p_row04_traceSegment_081_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 729 13 14, g32p_row04_traceSegment_081_0729_0013, g32p_row04_traceSegment_081_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 702 27 27, g32p_row04_traceSegment_081_0702_0027, g32p_row04_traceSegment_081_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 648 54 54, g32p_row04_traceSegment_081_0648_0054, g32p_row04_traceSegment_081_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 756 13 14, g32p_row04_traceSegment_081_0756_0013, g32p_row04_traceSegment_081_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 783 13 14, g32p_row04_traceSegment_081_0783_0013, g32p_row04_traceSegment_081_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 756 27 27, g32p_row04_traceSegment_081_0756_0027, g32p_row04_traceSegment_081_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 810 13 14, g32p_row04_traceSegment_081_0810_0013, g32p_row04_traceSegment_081_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 837 13 14, g32p_row04_traceSegment_081_0837_0013, g32p_row04_traceSegment_081_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 810 27 27, g32p_row04_traceSegment_081_0810_0027, g32p_row04_traceSegment_081_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 756 54 54, g32p_row04_traceSegment_081_0756_0054, g32p_row04_traceSegment_081_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_081 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 648 108 108, g32p_row04_traceSegment_081_0648_0108, g32p_row04_traceSegment_081_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_081 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 432 216 216, g32p_row04_traceSegment_081_0432_0216, g32p_row04_traceSegment_081_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_081 0 864 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 0 432 432, g32p_row04_traceSegment_081_0000_0432, g32p_row04_traceSegment_081_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 864 13 14, g32p_row04_traceSegment_081_0864_0013, g32p_row04_traceSegment_081_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 891 13 14, g32p_row04_traceSegment_081_0891_0013, g32p_row04_traceSegment_081_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 864 27 27, g32p_row04_traceSegment_081_0864_0027, g32p_row04_traceSegment_081_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 918 13 14, g32p_row04_traceSegment_081_0918_0013, g32p_row04_traceSegment_081_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 945 13 14, g32p_row04_traceSegment_081_0945_0013, g32p_row04_traceSegment_081_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 918 27 27, g32p_row04_traceSegment_081_0918_0027, g32p_row04_traceSegment_081_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 864 54 54, g32p_row04_traceSegment_081_0864_0054, g32p_row04_traceSegment_081_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 972 13 14, g32p_row04_traceSegment_081_0972_0013, g32p_row04_traceSegment_081_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 999 13 14, g32p_row04_traceSegment_081_0999_0013, g32p_row04_traceSegment_081_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 972 27 27, g32p_row04_traceSegment_081_0972_0027, g32p_row04_traceSegment_081_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1026 13 14, g32p_row04_traceSegment_081_1026_0013, g32p_row04_traceSegment_081_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1053 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1053 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1053 13 14, g32p_row04_traceSegment_081_1053_0013, g32p_row04_traceSegment_081_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1026 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1026 27 27, g32p_row04_traceSegment_081_1026_0027, g32p_row04_traceSegment_081_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 972 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 972 54 54, g32p_row04_traceSegment_081_0972_0054, g32p_row04_traceSegment_081_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_081 864 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 864 108 108, g32p_row04_traceSegment_081_0864_0108, g32p_row04_traceSegment_081_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1080 13 14, g32p_row04_traceSegment_081_1080_0013, g32p_row04_traceSegment_081_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1107 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1120 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1107 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1107 13 14, g32p_row04_traceSegment_081_1107_0013, g32p_row04_traceSegment_081_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1080 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1080 27 27, g32p_row04_traceSegment_081_1080_0027, g32p_row04_traceSegment_081_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1134 13 14, g32p_row04_traceSegment_081_1134_0013, g32p_row04_traceSegment_081_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1161 13 14, g32p_row04_traceSegment_081_1161_0013, g32p_row04_traceSegment_081_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1134 27 27, g32p_row04_traceSegment_081_1134_0027, g32p_row04_traceSegment_081_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 1080 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1080 54 54, g32p_row04_traceSegment_081_1080_0054, g32p_row04_traceSegment_081_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1188 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1188 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1188 13 14, g32p_row04_traceSegment_081_1188_0013, g32p_row04_traceSegment_081_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1215 13 14, g32p_row04_traceSegment_081_1215_0013, g32p_row04_traceSegment_081_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1188 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1188 27 27, g32p_row04_traceSegment_081_1188_0027, g32p_row04_traceSegment_081_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1242 13 14, g32p_row04_traceSegment_081_1242_0013, g32p_row04_traceSegment_081_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1269 13 14, g32p_row04_traceSegment_081_1269_0013, g32p_row04_traceSegment_081_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1242 27 27, g32p_row04_traceSegment_081_1242_0027, g32p_row04_traceSegment_081_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 1188 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1188 54 54, g32p_row04_traceSegment_081_1188_0054, g32p_row04_traceSegment_081_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_081 1080 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1080 108 108, g32p_row04_traceSegment_081_1080_0108, g32p_row04_traceSegment_081_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_081 864 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 864 216 216, g32p_row04_traceSegment_081_0864_0216, g32p_row04_traceSegment_081_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1296 13 14, g32p_row04_traceSegment_081_1296_0013, g32p_row04_traceSegment_081_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1323 13 14, g32p_row04_traceSegment_081_1323_0013, g32p_row04_traceSegment_081_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1296 27 27, g32p_row04_traceSegment_081_1296_0027, g32p_row04_traceSegment_081_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1350 13 14, g32p_row04_traceSegment_081_1350_0013, g32p_row04_traceSegment_081_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1377 13 14, g32p_row04_traceSegment_081_1377_0013, g32p_row04_traceSegment_081_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1350 27 27, g32p_row04_traceSegment_081_1350_0027, g32p_row04_traceSegment_081_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1296 54 54, g32p_row04_traceSegment_081_1296_0054, g32p_row04_traceSegment_081_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1404 13 14, g32p_row04_traceSegment_081_1404_0013, g32p_row04_traceSegment_081_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1431 13 14, g32p_row04_traceSegment_081_1431_0013, g32p_row04_traceSegment_081_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1404 27 27, g32p_row04_traceSegment_081_1404_0027, g32p_row04_traceSegment_081_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1458 13 14, g32p_row04_traceSegment_081_1458_0013, g32p_row04_traceSegment_081_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1485 13 14, g32p_row04_traceSegment_081_1485_0013, g32p_row04_traceSegment_081_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1458 27 27, g32p_row04_traceSegment_081_1458_0027, g32p_row04_traceSegment_081_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1404 54 54, g32p_row04_traceSegment_081_1404_0054, g32p_row04_traceSegment_081_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_081 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1296 108 108, g32p_row04_traceSegment_081_1296_0108, g32p_row04_traceSegment_081_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1512 13 14, g32p_row04_traceSegment_081_1512_0013, g32p_row04_traceSegment_081_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1539 13 14, g32p_row04_traceSegment_081_1539_0013, g32p_row04_traceSegment_081_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1512 27 27, g32p_row04_traceSegment_081_1512_0027, g32p_row04_traceSegment_081_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1566 13 14, g32p_row04_traceSegment_081_1566_0013, g32p_row04_traceSegment_081_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1593 13 14, g32p_row04_traceSegment_081_1593_0013, g32p_row04_traceSegment_081_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1566 27 27, g32p_row04_traceSegment_081_1566_0027, g32p_row04_traceSegment_081_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1512 54 54, g32p_row04_traceSegment_081_1512_0054, g32p_row04_traceSegment_081_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1620 13 14, g32p_row04_traceSegment_081_1620_0013, g32p_row04_traceSegment_081_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1647 13 14, g32p_row04_traceSegment_081_1647_0013, g32p_row04_traceSegment_081_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1620 27 27, g32p_row04_traceSegment_081_1620_0027, g32p_row04_traceSegment_081_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1674 13 14, g32p_row04_traceSegment_081_1674_0013, g32p_row04_traceSegment_081_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_081 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_081 1714 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_081_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_081 1701 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1701 13 14, g32p_row04_traceSegment_081_1701_0013, g32p_row04_traceSegment_081_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_081 1674 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1674 27 27, g32p_row04_traceSegment_081_1674_0027, g32p_row04_traceSegment_081_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_081 1620 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1620 54 54, g32p_row04_traceSegment_081_1620_0054, g32p_row04_traceSegment_081_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_081 1512 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1512 108 108, g32p_row04_traceSegment_081_1512_0108, g32p_row04_traceSegment_081_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_081_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_081 1296 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 1296 216 216, g32p_row04_traceSegment_081_1296_0216, g32p_row04_traceSegment_081_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_081 864 864 = [1, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 864 432 432, g32p_row04_traceSegment_081_0864_0432, g32p_row04_traceSegment_081_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_081_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_081 0 1728 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_081 0 864 864, g32p_row04_traceSegment_081_0000_0864, g32p_row04_traceSegment_081_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 81 = [4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_081_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_082 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 82 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_082_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 0 13 14, g32p_row04_traceSegment_082_0000_0013, g32p_row04_traceSegment_082_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 27 13 14, g32p_row04_traceSegment_082_0027_0013, g32p_row04_traceSegment_082_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 0 27 27, g32p_row04_traceSegment_082_0000_0027, g32p_row04_traceSegment_082_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 54 13 14, g32p_row04_traceSegment_082_0054_0013, g32p_row04_traceSegment_082_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 81 13 14, g32p_row04_traceSegment_082_0081_0013, g32p_row04_traceSegment_082_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 54 27 27, g32p_row04_traceSegment_082_0054_0027, g32p_row04_traceSegment_082_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 0 54 54, g32p_row04_traceSegment_082_0000_0054, g32p_row04_traceSegment_082_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 108 13 14, g32p_row04_traceSegment_082_0108_0013, g32p_row04_traceSegment_082_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 135 13 14, g32p_row04_traceSegment_082_0135_0013, g32p_row04_traceSegment_082_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 108 27 27, g32p_row04_traceSegment_082_0108_0027, g32p_row04_traceSegment_082_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 162 13 14, g32p_row04_traceSegment_082_0162_0013, g32p_row04_traceSegment_082_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 189 13 14, g32p_row04_traceSegment_082_0189_0013, g32p_row04_traceSegment_082_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 162 27 27, g32p_row04_traceSegment_082_0162_0027, g32p_row04_traceSegment_082_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 108 54 54, g32p_row04_traceSegment_082_0108_0054, g32p_row04_traceSegment_082_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_082 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 0 108 108, g32p_row04_traceSegment_082_0000_0108, g32p_row04_traceSegment_082_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 216 13 14, g32p_row04_traceSegment_082_0216_0013, g32p_row04_traceSegment_082_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 243 13 14, g32p_row04_traceSegment_082_0243_0013, g32p_row04_traceSegment_082_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 216 27 27, g32p_row04_traceSegment_082_0216_0027, g32p_row04_traceSegment_082_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 270 13 14, g32p_row04_traceSegment_082_0270_0013, g32p_row04_traceSegment_082_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 297 13 14, g32p_row04_traceSegment_082_0297_0013, g32p_row04_traceSegment_082_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 270 27 27, g32p_row04_traceSegment_082_0270_0027, g32p_row04_traceSegment_082_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 216 54 54, g32p_row04_traceSegment_082_0216_0054, g32p_row04_traceSegment_082_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 324 13 14, g32p_row04_traceSegment_082_0324_0013, g32p_row04_traceSegment_082_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 351 13 14, g32p_row04_traceSegment_082_0351_0013, g32p_row04_traceSegment_082_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 324 27 27, g32p_row04_traceSegment_082_0324_0027, g32p_row04_traceSegment_082_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 378 13 14, g32p_row04_traceSegment_082_0378_0013, g32p_row04_traceSegment_082_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 405 13 14, g32p_row04_traceSegment_082_0405_0013, g32p_row04_traceSegment_082_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 378 27 27, g32p_row04_traceSegment_082_0378_0027, g32p_row04_traceSegment_082_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 324 54 54, g32p_row04_traceSegment_082_0324_0054, g32p_row04_traceSegment_082_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_082 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 216 108 108, g32p_row04_traceSegment_082_0216_0108, g32p_row04_traceSegment_082_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_082 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 0 216 216, g32p_row04_traceSegment_082_0000_0216, g32p_row04_traceSegment_082_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 432 13 14, g32p_row04_traceSegment_082_0432_0013, g32p_row04_traceSegment_082_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 459 13 14, g32p_row04_traceSegment_082_0459_0013, g32p_row04_traceSegment_082_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 432 27 27, g32p_row04_traceSegment_082_0432_0027, g32p_row04_traceSegment_082_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 486 13 14, g32p_row04_traceSegment_082_0486_0013, g32p_row04_traceSegment_082_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 513 13 14, g32p_row04_traceSegment_082_0513_0013, g32p_row04_traceSegment_082_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 486 27 27, g32p_row04_traceSegment_082_0486_0027, g32p_row04_traceSegment_082_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 432 54 54, g32p_row04_traceSegment_082_0432_0054, g32p_row04_traceSegment_082_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 553 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 540 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 540 13 14, g32p_row04_traceSegment_082_0540_0013, g32p_row04_traceSegment_082_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 567 13 14, g32p_row04_traceSegment_082_0567_0013, g32p_row04_traceSegment_082_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 540 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 540 27 27, g32p_row04_traceSegment_082_0540_0027, g32p_row04_traceSegment_082_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 594 13 14, g32p_row04_traceSegment_082_0594_0013, g32p_row04_traceSegment_082_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 621 13 14, g32p_row04_traceSegment_082_0621_0013, g32p_row04_traceSegment_082_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 594 27 27, g32p_row04_traceSegment_082_0594_0027, g32p_row04_traceSegment_082_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 540 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 540 54 54, g32p_row04_traceSegment_082_0540_0054, g32p_row04_traceSegment_082_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_082 432 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 432 108 108, g32p_row04_traceSegment_082_0432_0108, g32p_row04_traceSegment_082_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 648 13 14, g32p_row04_traceSegment_082_0648_0013, g32p_row04_traceSegment_082_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 675 13 14, g32p_row04_traceSegment_082_0675_0013, g32p_row04_traceSegment_082_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 648 27 27, g32p_row04_traceSegment_082_0648_0027, g32p_row04_traceSegment_082_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 702 13 14, g32p_row04_traceSegment_082_0702_0013, g32p_row04_traceSegment_082_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 729 13 14, g32p_row04_traceSegment_082_0729_0013, g32p_row04_traceSegment_082_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 702 27 27, g32p_row04_traceSegment_082_0702_0027, g32p_row04_traceSegment_082_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 648 54 54, g32p_row04_traceSegment_082_0648_0054, g32p_row04_traceSegment_082_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 756 13 14, g32p_row04_traceSegment_082_0756_0013, g32p_row04_traceSegment_082_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 783 13 14, g32p_row04_traceSegment_082_0783_0013, g32p_row04_traceSegment_082_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 756 27 27, g32p_row04_traceSegment_082_0756_0027, g32p_row04_traceSegment_082_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 810 13 14, g32p_row04_traceSegment_082_0810_0013, g32p_row04_traceSegment_082_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 837 13 14, g32p_row04_traceSegment_082_0837_0013, g32p_row04_traceSegment_082_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 810 27 27, g32p_row04_traceSegment_082_0810_0027, g32p_row04_traceSegment_082_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 756 54 54, g32p_row04_traceSegment_082_0756_0054, g32p_row04_traceSegment_082_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_082 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 648 108 108, g32p_row04_traceSegment_082_0648_0108, g32p_row04_traceSegment_082_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_082 432 432 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 432 216 216, g32p_row04_traceSegment_082_0432_0216, g32p_row04_traceSegment_082_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_082 0 864 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 0 432 432, g32p_row04_traceSegment_082_0000_0432, g32p_row04_traceSegment_082_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 864 13 14, g32p_row04_traceSegment_082_0864_0013, g32p_row04_traceSegment_082_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 891 13 14, g32p_row04_traceSegment_082_0891_0013, g32p_row04_traceSegment_082_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 864 27 27, g32p_row04_traceSegment_082_0864_0027, g32p_row04_traceSegment_082_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 918 13 14, g32p_row04_traceSegment_082_0918_0013, g32p_row04_traceSegment_082_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 945 13 14, g32p_row04_traceSegment_082_0945_0013, g32p_row04_traceSegment_082_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 918 27 27, g32p_row04_traceSegment_082_0918_0027, g32p_row04_traceSegment_082_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 864 54 54, g32p_row04_traceSegment_082_0864_0054, g32p_row04_traceSegment_082_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 972 13 14, g32p_row04_traceSegment_082_0972_0013, g32p_row04_traceSegment_082_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 999 13 14, g32p_row04_traceSegment_082_0999_0013, g32p_row04_traceSegment_082_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 972 27 27, g32p_row04_traceSegment_082_0972_0027, g32p_row04_traceSegment_082_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1026 13 14, g32p_row04_traceSegment_082_1026_0013, g32p_row04_traceSegment_082_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1053 13 14, g32p_row04_traceSegment_082_1053_0013, g32p_row04_traceSegment_082_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1026 27 27, g32p_row04_traceSegment_082_1026_0027, g32p_row04_traceSegment_082_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 972 54 54, g32p_row04_traceSegment_082_0972_0054, g32p_row04_traceSegment_082_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_082 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 864 108 108, g32p_row04_traceSegment_082_0864_0108, g32p_row04_traceSegment_082_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1080 13 14, g32p_row04_traceSegment_082_1080_0013, g32p_row04_traceSegment_082_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1107 13 14, g32p_row04_traceSegment_082_1107_0013, g32p_row04_traceSegment_082_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1080 27 27, g32p_row04_traceSegment_082_1080_0027, g32p_row04_traceSegment_082_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1134 13 14, g32p_row04_traceSegment_082_1134_0013, g32p_row04_traceSegment_082_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1161 13 14, g32p_row04_traceSegment_082_1161_0013, g32p_row04_traceSegment_082_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1134 27 27, g32p_row04_traceSegment_082_1134_0027, g32p_row04_traceSegment_082_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1080 54 54, g32p_row04_traceSegment_082_1080_0054, g32p_row04_traceSegment_082_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1188 13 14, g32p_row04_traceSegment_082_1188_0013, g32p_row04_traceSegment_082_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1215 13 14, g32p_row04_traceSegment_082_1215_0013, g32p_row04_traceSegment_082_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1188 27 27, g32p_row04_traceSegment_082_1188_0027, g32p_row04_traceSegment_082_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1242 13 14, g32p_row04_traceSegment_082_1242_0013, g32p_row04_traceSegment_082_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1269 13 14, g32p_row04_traceSegment_082_1269_0013, g32p_row04_traceSegment_082_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1242 27 27, g32p_row04_traceSegment_082_1242_0027, g32p_row04_traceSegment_082_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1188 54 54, g32p_row04_traceSegment_082_1188_0054, g32p_row04_traceSegment_082_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_082 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1080 108 108, g32p_row04_traceSegment_082_1080_0108, g32p_row04_traceSegment_082_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_082 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 864 216 216, g32p_row04_traceSegment_082_0864_0216, g32p_row04_traceSegment_082_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1296 13 14, g32p_row04_traceSegment_082_1296_0013, g32p_row04_traceSegment_082_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1323 13 14, g32p_row04_traceSegment_082_1323_0013, g32p_row04_traceSegment_082_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1296 27 27, g32p_row04_traceSegment_082_1296_0027, g32p_row04_traceSegment_082_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1350 13 14, g32p_row04_traceSegment_082_1350_0013, g32p_row04_traceSegment_082_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1377 13 14, g32p_row04_traceSegment_082_1377_0013, g32p_row04_traceSegment_082_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1350 27 27, g32p_row04_traceSegment_082_1350_0027, g32p_row04_traceSegment_082_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1296 54 54, g32p_row04_traceSegment_082_1296_0054, g32p_row04_traceSegment_082_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1404 13 14, g32p_row04_traceSegment_082_1404_0013, g32p_row04_traceSegment_082_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1431 13 14, g32p_row04_traceSegment_082_1431_0013, g32p_row04_traceSegment_082_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1404 27 27, g32p_row04_traceSegment_082_1404_0027, g32p_row04_traceSegment_082_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1458 13 14, g32p_row04_traceSegment_082_1458_0013, g32p_row04_traceSegment_082_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1485 13 14, g32p_row04_traceSegment_082_1485_0013, g32p_row04_traceSegment_082_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1458 27 27, g32p_row04_traceSegment_082_1458_0027, g32p_row04_traceSegment_082_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1404 54 54, g32p_row04_traceSegment_082_1404_0054, g32p_row04_traceSegment_082_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_082 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1296 108 108, g32p_row04_traceSegment_082_1296_0108, g32p_row04_traceSegment_082_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1512 13 14, g32p_row04_traceSegment_082_1512_0013, g32p_row04_traceSegment_082_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1539 13 14, g32p_row04_traceSegment_082_1539_0013, g32p_row04_traceSegment_082_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1512 27 27, g32p_row04_traceSegment_082_1512_0027, g32p_row04_traceSegment_082_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1566 13 14, g32p_row04_traceSegment_082_1566_0013, g32p_row04_traceSegment_082_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1606 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1593 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1593 13 14, g32p_row04_traceSegment_082_1593_0013, g32p_row04_traceSegment_082_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1566 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1566 27 27, g32p_row04_traceSegment_082_1566_0027, g32p_row04_traceSegment_082_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 1512 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1512 54 54, g32p_row04_traceSegment_082_1512_0054, g32p_row04_traceSegment_082_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1620 13 14, g32p_row04_traceSegment_082_1620_0013, g32p_row04_traceSegment_082_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1647 13 14, g32p_row04_traceSegment_082_1647_0013, g32p_row04_traceSegment_082_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1620 27 27, g32p_row04_traceSegment_082_1620_0027, g32p_row04_traceSegment_082_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1674 13 14, g32p_row04_traceSegment_082_1674_0013, g32p_row04_traceSegment_082_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_082 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_082 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_082_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_082 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1701 13 14, g32p_row04_traceSegment_082_1701_0013, g32p_row04_traceSegment_082_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_082 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1674 27 27, g32p_row04_traceSegment_082_1674_0027, g32p_row04_traceSegment_082_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_082 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1620 54 54, g32p_row04_traceSegment_082_1620_0054, g32p_row04_traceSegment_082_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_082 1512 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1512 108 108, g32p_row04_traceSegment_082_1512_0108, g32p_row04_traceSegment_082_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_082_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_082 1296 432 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 1296 216 216, g32p_row04_traceSegment_082_1296_0216, g32p_row04_traceSegment_082_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_082 864 864 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 864 432 432, g32p_row04_traceSegment_082_0864_0432, g32p_row04_traceSegment_082_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_082_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_082 0 1728 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_082 0 864 864, g32p_row04_traceSegment_082_0000_0864, g32p_row04_traceSegment_082_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 82 = [0, 2] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_082_0000_1728

end HodgeLean.Foundations.Program

end
end
