import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0302

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_057 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 57 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_057_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 0 13 14, g32p_row02_traceSegment_057_0000_0013, g32p_row02_traceSegment_057_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 27 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 40 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 27 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 27 13 14, g32p_row02_traceSegment_057_0027_0013, g32p_row02_traceSegment_057_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 0 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 0 27 27, g32p_row02_traceSegment_057_0000_0027, g32p_row02_traceSegment_057_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 54 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 67 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 54 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 54 13 14, g32p_row02_traceSegment_057_0054_0013, g32p_row02_traceSegment_057_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 81 13 14, g32p_row02_traceSegment_057_0081_0013, g32p_row02_traceSegment_057_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 54 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 54 27 27, g32p_row02_traceSegment_057_0054_0027, g32p_row02_traceSegment_057_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 0 108 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 0 54 54, g32p_row02_traceSegment_057_0000_0054, g32p_row02_traceSegment_057_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 108 13 14, g32p_row02_traceSegment_057_0108_0013, g32p_row02_traceSegment_057_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 135 13 14, g32p_row02_traceSegment_057_0135_0013, g32p_row02_traceSegment_057_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 108 27 27, g32p_row02_traceSegment_057_0108_0027, g32p_row02_traceSegment_057_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 162 13 14, g32p_row02_traceSegment_057_0162_0013, g32p_row02_traceSegment_057_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 189 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 189 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 189 13 14, g32p_row02_traceSegment_057_0189_0013, g32p_row02_traceSegment_057_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 162 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 162 27 27, g32p_row02_traceSegment_057_0162_0027, g32p_row02_traceSegment_057_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 108 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 108 54 54, g32p_row02_traceSegment_057_0108_0054, g32p_row02_traceSegment_057_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 0 216 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 0 108 108, g32p_row02_traceSegment_057_0000_0108, g32p_row02_traceSegment_057_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 216 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 216 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 216 13 14, g32p_row02_traceSegment_057_0216_0013, g32p_row02_traceSegment_057_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 243 13 14, g32p_row02_traceSegment_057_0243_0013, g32p_row02_traceSegment_057_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 216 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 216 27 27, g32p_row02_traceSegment_057_0216_0027, g32p_row02_traceSegment_057_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 270 13 14, g32p_row02_traceSegment_057_0270_0013, g32p_row02_traceSegment_057_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 297 13 14, g32p_row02_traceSegment_057_0297_0013, g32p_row02_traceSegment_057_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 270 27 27, g32p_row02_traceSegment_057_0270_0027, g32p_row02_traceSegment_057_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 216 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 216 54 54, g32p_row02_traceSegment_057_0216_0054, g32p_row02_traceSegment_057_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 324 13 14, g32p_row02_traceSegment_057_0324_0013, g32p_row02_traceSegment_057_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 351 13 14, g32p_row02_traceSegment_057_0351_0013, g32p_row02_traceSegment_057_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 324 27 27, g32p_row02_traceSegment_057_0324_0027, g32p_row02_traceSegment_057_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 378 13 14, g32p_row02_traceSegment_057_0378_0013, g32p_row02_traceSegment_057_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 405 13 14, g32p_row02_traceSegment_057_0405_0013, g32p_row02_traceSegment_057_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 378 27 27, g32p_row02_traceSegment_057_0378_0027, g32p_row02_traceSegment_057_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 324 54 54, g32p_row02_traceSegment_057_0324_0054, g32p_row02_traceSegment_057_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 216 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 216 108 108, g32p_row02_traceSegment_057_0216_0108, g32p_row02_traceSegment_057_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_057 0 432 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 0 216 216, g32p_row02_traceSegment_057_0000_0216, g32p_row02_traceSegment_057_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 432 13 14, g32p_row02_traceSegment_057_0432_0013, g32p_row02_traceSegment_057_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 459 13 14, g32p_row02_traceSegment_057_0459_0013, g32p_row02_traceSegment_057_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 432 27 27, g32p_row02_traceSegment_057_0432_0027, g32p_row02_traceSegment_057_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 486 13 14, g32p_row02_traceSegment_057_0486_0013, g32p_row02_traceSegment_057_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 513 13 14, g32p_row02_traceSegment_057_0513_0013, g32p_row02_traceSegment_057_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 486 27 27, g32p_row02_traceSegment_057_0486_0027, g32p_row02_traceSegment_057_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 432 54 54, g32p_row02_traceSegment_057_0432_0054, g32p_row02_traceSegment_057_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 540 13 14, g32p_row02_traceSegment_057_0540_0013, g32p_row02_traceSegment_057_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 567 13 14, g32p_row02_traceSegment_057_0567_0013, g32p_row02_traceSegment_057_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 540 27 27, g32p_row02_traceSegment_057_0540_0027, g32p_row02_traceSegment_057_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 607 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 594 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 594 13 14, g32p_row02_traceSegment_057_0594_0013, g32p_row02_traceSegment_057_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 621 13 14, g32p_row02_traceSegment_057_0621_0013, g32p_row02_traceSegment_057_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 594 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 594 27 27, g32p_row02_traceSegment_057_0594_0027, g32p_row02_traceSegment_057_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 540 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 540 54 54, g32p_row02_traceSegment_057_0540_0054, g32p_row02_traceSegment_057_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 432 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 432 108 108, g32p_row02_traceSegment_057_0432_0108, g32p_row02_traceSegment_057_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 648 13 14, g32p_row02_traceSegment_057_0648_0013, g32p_row02_traceSegment_057_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 675 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 688 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 675 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 675 13 14, g32p_row02_traceSegment_057_0675_0013, g32p_row02_traceSegment_057_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 648 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 648 27 27, g32p_row02_traceSegment_057_0648_0027, g32p_row02_traceSegment_057_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 702 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 702 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 702 13 14, g32p_row02_traceSegment_057_0702_0013, g32p_row02_traceSegment_057_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 729 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 742 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 729 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 729 13 14, g32p_row02_traceSegment_057_0729_0013, g32p_row02_traceSegment_057_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 702 54 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 702 27 27, g32p_row02_traceSegment_057_0702_0027, g32p_row02_traceSegment_057_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 648 108 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 648 54 54, g32p_row02_traceSegment_057_0648_0054, g32p_row02_traceSegment_057_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 756 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 769 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 756 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 756 13 14, g32p_row02_traceSegment_057_0756_0013, g32p_row02_traceSegment_057_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 783 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 783 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 783 13 14, g32p_row02_traceSegment_057_0783_0013, g32p_row02_traceSegment_057_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 756 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 756 27 27, g32p_row02_traceSegment_057_0756_0027, g32p_row02_traceSegment_057_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 810 13 14, g32p_row02_traceSegment_057_0810_0013, g32p_row02_traceSegment_057_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 837 13 14, g32p_row02_traceSegment_057_0837_0013, g32p_row02_traceSegment_057_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 810 27 27, g32p_row02_traceSegment_057_0810_0027, g32p_row02_traceSegment_057_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 756 108 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 756 54 54, g32p_row02_traceSegment_057_0756_0054, g32p_row02_traceSegment_057_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 648 216 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 648 108 108, g32p_row02_traceSegment_057_0648_0108, g32p_row02_traceSegment_057_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_057 432 432 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 432 216 216, g32p_row02_traceSegment_057_0432_0216, g32p_row02_traceSegment_057_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_057 0 864 = [0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 0 432 432, g32p_row02_traceSegment_057_0000_0432, g32p_row02_traceSegment_057_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 864 13 14, g32p_row02_traceSegment_057_0864_0013, g32p_row02_traceSegment_057_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 891 13 14, g32p_row02_traceSegment_057_0891_0013, g32p_row02_traceSegment_057_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 864 27 27, g32p_row02_traceSegment_057_0864_0027, g32p_row02_traceSegment_057_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 918 13 14, g32p_row02_traceSegment_057_0918_0013, g32p_row02_traceSegment_057_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 945 13 14, g32p_row02_traceSegment_057_0945_0013, g32p_row02_traceSegment_057_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 918 27 27, g32p_row02_traceSegment_057_0918_0027, g32p_row02_traceSegment_057_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 864 54 54, g32p_row02_traceSegment_057_0864_0054, g32p_row02_traceSegment_057_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 972 13 14, g32p_row02_traceSegment_057_0972_0013, g32p_row02_traceSegment_057_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1012 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 999 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 999 13 14, g32p_row02_traceSegment_057_0999_0013, g32p_row02_traceSegment_057_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 972 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 972 27 27, g32p_row02_traceSegment_057_0972_0027, g32p_row02_traceSegment_057_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1026 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1039 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1026 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1026 13 14, g32p_row02_traceSegment_057_1026_0013, g32p_row02_traceSegment_057_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1053 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1066 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1053 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1053 13 14, g32p_row02_traceSegment_057_1053_0013, g32p_row02_traceSegment_057_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1026 54 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1026 27 27, g32p_row02_traceSegment_057_1026_0027, g32p_row02_traceSegment_057_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 972 108 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 972 54 54, g32p_row02_traceSegment_057_0972_0054, g32p_row02_traceSegment_057_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 864 216 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 864 108 108, g32p_row02_traceSegment_057_0864_0108, g32p_row02_traceSegment_057_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1080 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1093 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1080 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1080 13 14, g32p_row02_traceSegment_057_1080_0013, g32p_row02_traceSegment_057_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1107 13 14, g32p_row02_traceSegment_057_1107_0013, g32p_row02_traceSegment_057_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1080 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1080 27 27, g32p_row02_traceSegment_057_1080_0027, g32p_row02_traceSegment_057_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1134 13 14, g32p_row02_traceSegment_057_1134_0013, g32p_row02_traceSegment_057_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1161 13 14, g32p_row02_traceSegment_057_1161_0013, g32p_row02_traceSegment_057_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1134 27 27, g32p_row02_traceSegment_057_1134_0027, g32p_row02_traceSegment_057_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 1080 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1080 54 54, g32p_row02_traceSegment_057_1080_0054, g32p_row02_traceSegment_057_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1188 13 14, g32p_row02_traceSegment_057_1188_0013, g32p_row02_traceSegment_057_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1215 13 14, g32p_row02_traceSegment_057_1215_0013, g32p_row02_traceSegment_057_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1188 27 27, g32p_row02_traceSegment_057_1188_0027, g32p_row02_traceSegment_057_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1242 13 14, g32p_row02_traceSegment_057_1242_0013, g32p_row02_traceSegment_057_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1269 13 14, g32p_row02_traceSegment_057_1269_0013, g32p_row02_traceSegment_057_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1242 27 27, g32p_row02_traceSegment_057_1242_0027, g32p_row02_traceSegment_057_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1188 54 54, g32p_row02_traceSegment_057_1188_0054, g32p_row02_traceSegment_057_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 1080 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1080 108 108, g32p_row02_traceSegment_057_1080_0108, g32p_row02_traceSegment_057_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_057 864 432 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 864 216 216, g32p_row02_traceSegment_057_0864_0216, g32p_row02_traceSegment_057_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1296 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1309 14 = [0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1296 27 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1296 13 14, g32p_row02_traceSegment_057_1296_0013, g32p_row02_traceSegment_057_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1323 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1323 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1323 13 14, g32p_row02_traceSegment_057_1323_0013, g32p_row02_traceSegment_057_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1296 54 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1296 27 27, g32p_row02_traceSegment_057_1296_0027, g32p_row02_traceSegment_057_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1350 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1363 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1350 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1350 13 14, g32p_row02_traceSegment_057_1350_0013, g32p_row02_traceSegment_057_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1377 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1390 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1377 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1377 13 14, g32p_row02_traceSegment_057_1377_0013, g32p_row02_traceSegment_057_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1350 54 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1350 27 27, g32p_row02_traceSegment_057_1350_0027, g32p_row02_traceSegment_057_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 1296 108 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1296 54 54, g32p_row02_traceSegment_057_1296_0054, g32p_row02_traceSegment_057_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1404 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1417 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1404 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1404 13 14, g32p_row02_traceSegment_057_1404_0013, g32p_row02_traceSegment_057_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1431 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1444 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1431 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1431 13 14, g32p_row02_traceSegment_057_1431_0013, g32p_row02_traceSegment_057_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1404 54 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1404 27 27, g32p_row02_traceSegment_057_1404_0027, g32p_row02_traceSegment_057_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1458 13 14, g32p_row02_traceSegment_057_1458_0013, g32p_row02_traceSegment_057_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1485 13 14, g32p_row02_traceSegment_057_1485_0013, g32p_row02_traceSegment_057_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1458 27 27, g32p_row02_traceSegment_057_1458_0027, g32p_row02_traceSegment_057_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 1404 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1404 54 54, g32p_row02_traceSegment_057_1404_0054, g32p_row02_traceSegment_057_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 1296 216 = [0, 26] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1296 108 108, g32p_row02_traceSegment_057_1296_0108, g32p_row02_traceSegment_057_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1512 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1525 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1512 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1512 13 14, g32p_row02_traceSegment_057_1512_0013, g32p_row02_traceSegment_057_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1539 13 14, g32p_row02_traceSegment_057_1539_0013, g32p_row02_traceSegment_057_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1512 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1512 27 27, g32p_row02_traceSegment_057_1512_0027, g32p_row02_traceSegment_057_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1566 13 14, g32p_row02_traceSegment_057_1566_0013, g32p_row02_traceSegment_057_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1606 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1593 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1593 13 14, g32p_row02_traceSegment_057_1593_0013, g32p_row02_traceSegment_057_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1566 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1566 27 27, g32p_row02_traceSegment_057_1566_0027, g32p_row02_traceSegment_057_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 1512 108 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1512 54 54, g32p_row02_traceSegment_057_1512_0054, g32p_row02_traceSegment_057_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1620 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1620 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1620 13 14, g32p_row02_traceSegment_057_1620_0013, g32p_row02_traceSegment_057_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1647 13 14, g32p_row02_traceSegment_057_1647_0013, g32p_row02_traceSegment_057_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1620 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1620 27 27, g32p_row02_traceSegment_057_1620_0027, g32p_row02_traceSegment_057_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1674 13 14, g32p_row02_traceSegment_057_1674_0013, g32p_row02_traceSegment_057_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1701 13 14, g32p_row02_traceSegment_057_1701_0013, g32p_row02_traceSegment_057_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1674 27 27, g32p_row02_traceSegment_057_1674_0027, g32p_row02_traceSegment_057_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 1620 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1620 54 54, g32p_row02_traceSegment_057_1620_0054, g32p_row02_traceSegment_057_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 1512 216 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1512 108 108, g32p_row02_traceSegment_057_1512_0108, g32p_row02_traceSegment_057_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_057 1296 432 = [0, 34] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1296 216 216, g32p_row02_traceSegment_057_1296_0216, g32p_row02_traceSegment_057_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_057 864 864 = [0, 46] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 864 432 432, g32p_row02_traceSegment_057_0864_0432, g32p_row02_traceSegment_057_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_057 0 1728 = [0, 70] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 0 864 864, g32p_row02_traceSegment_057_0000_0864, g32p_row02_traceSegment_057_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1728 13 14, g32p_row02_traceSegment_057_1728_0013, g32p_row02_traceSegment_057_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1768 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1755 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1755 13 14, g32p_row02_traceSegment_057_1755_0013, g32p_row02_traceSegment_057_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1728 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1728 27 27, g32p_row02_traceSegment_057_1728_0027, g32p_row02_traceSegment_057_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1782 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1795 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1782 27 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1782 13 14, g32p_row02_traceSegment_057_1782_0013, g32p_row02_traceSegment_057_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1809 13 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1822 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1809 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1809 13 14, g32p_row02_traceSegment_057_1809_0013, g32p_row02_traceSegment_057_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1782 54 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1782 27 27, g32p_row02_traceSegment_057_1782_0027, g32p_row02_traceSegment_057_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 1728 108 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1728 54 54, g32p_row02_traceSegment_057_1728_0054, g32p_row02_traceSegment_057_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1836 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1849 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1836 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1836 13 14, g32p_row02_traceSegment_057_1836_0013, g32p_row02_traceSegment_057_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1876 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1863 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1863 13 14, g32p_row02_traceSegment_057_1863_0013, g32p_row02_traceSegment_057_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1836 54 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1836 27 27, g32p_row02_traceSegment_057_1836_0027, g32p_row02_traceSegment_057_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1890 13 14, g32p_row02_traceSegment_057_1890_0013, g32p_row02_traceSegment_057_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1917 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1917 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1917 13 14, g32p_row02_traceSegment_057_1917_0013, g32p_row02_traceSegment_057_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1890 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1890 27 27, g32p_row02_traceSegment_057_1890_0027, g32p_row02_traceSegment_057_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 1836 108 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1836 54 54, g32p_row02_traceSegment_057_1836_0054, g32p_row02_traceSegment_057_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 1728 216 = [0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1728 108 108, g32p_row02_traceSegment_057_1728_0108, g32p_row02_traceSegment_057_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1944 13 14, g32p_row02_traceSegment_057_1944_0013, g32p_row02_traceSegment_057_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1971 13 14, g32p_row02_traceSegment_057_1971_0013, g32p_row02_traceSegment_057_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1944 27 27, g32p_row02_traceSegment_057_1944_0027, g32p_row02_traceSegment_057_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1998 13 14, g32p_row02_traceSegment_057_1998_0013, g32p_row02_traceSegment_057_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2025 13 14, g32p_row02_traceSegment_057_2025_0013, g32p_row02_traceSegment_057_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1998 27 27, g32p_row02_traceSegment_057_1998_0027, g32p_row02_traceSegment_057_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1944 54 54, g32p_row02_traceSegment_057_1944_0054, g32p_row02_traceSegment_057_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2052 13 14, g32p_row02_traceSegment_057_2052_0013, g32p_row02_traceSegment_057_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2079 13 14, g32p_row02_traceSegment_057_2079_0013, g32p_row02_traceSegment_057_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2052 27 27, g32p_row02_traceSegment_057_2052_0027, g32p_row02_traceSegment_057_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2106 13 14, g32p_row02_traceSegment_057_2106_0013, g32p_row02_traceSegment_057_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2133 13 14, g32p_row02_traceSegment_057_2133_0013, g32p_row02_traceSegment_057_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2106 27 27, g32p_row02_traceSegment_057_2106_0027, g32p_row02_traceSegment_057_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2052 54 54, g32p_row02_traceSegment_057_2052_0054, g32p_row02_traceSegment_057_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1944 108 108, g32p_row02_traceSegment_057_1944_0108, g32p_row02_traceSegment_057_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_057 1728 432 = [0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1728 216 216, g32p_row02_traceSegment_057_1728_0216, g32p_row02_traceSegment_057_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2160 13 14, g32p_row02_traceSegment_057_2160_0013, g32p_row02_traceSegment_057_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2187 13 14, g32p_row02_traceSegment_057_2187_0013, g32p_row02_traceSegment_057_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2160 27 27, g32p_row02_traceSegment_057_2160_0027, g32p_row02_traceSegment_057_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2214 13 14, g32p_row02_traceSegment_057_2214_0013, g32p_row02_traceSegment_057_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2241 13 14, g32p_row02_traceSegment_057_2241_0013, g32p_row02_traceSegment_057_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2214 27 27, g32p_row02_traceSegment_057_2214_0027, g32p_row02_traceSegment_057_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2160 54 54, g32p_row02_traceSegment_057_2160_0054, g32p_row02_traceSegment_057_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2268 13 14, g32p_row02_traceSegment_057_2268_0013, g32p_row02_traceSegment_057_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2295 13 14, g32p_row02_traceSegment_057_2295_0013, g32p_row02_traceSegment_057_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2268 27 27, g32p_row02_traceSegment_057_2268_0027, g32p_row02_traceSegment_057_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2322 13 14, g32p_row02_traceSegment_057_2322_0013, g32p_row02_traceSegment_057_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2349 13 14, g32p_row02_traceSegment_057_2349_0013, g32p_row02_traceSegment_057_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2322 27 27, g32p_row02_traceSegment_057_2322_0027, g32p_row02_traceSegment_057_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2268 54 54, g32p_row02_traceSegment_057_2268_0054, g32p_row02_traceSegment_057_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2160 108 108, g32p_row02_traceSegment_057_2160_0108, g32p_row02_traceSegment_057_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2376 13 14, g32p_row02_traceSegment_057_2376_0013, g32p_row02_traceSegment_057_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2403 13 14, g32p_row02_traceSegment_057_2403_0013, g32p_row02_traceSegment_057_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2376 27 27, g32p_row02_traceSegment_057_2376_0027, g32p_row02_traceSegment_057_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2430 13 14, g32p_row02_traceSegment_057_2430_0013, g32p_row02_traceSegment_057_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2457 13 14, g32p_row02_traceSegment_057_2457_0013, g32p_row02_traceSegment_057_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2430 27 27, g32p_row02_traceSegment_057_2430_0027, g32p_row02_traceSegment_057_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2376 54 54, g32p_row02_traceSegment_057_2376_0054, g32p_row02_traceSegment_057_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2484 13 14, g32p_row02_traceSegment_057_2484_0013, g32p_row02_traceSegment_057_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2511 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2511 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2511 13 14, g32p_row02_traceSegment_057_2511_0013, g32p_row02_traceSegment_057_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2484 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2484 27 27, g32p_row02_traceSegment_057_2484_0027, g32p_row02_traceSegment_057_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2538 13 14, g32p_row02_traceSegment_057_2538_0013, g32p_row02_traceSegment_057_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2565 13 14, g32p_row02_traceSegment_057_2565_0013, g32p_row02_traceSegment_057_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2538 27 27, g32p_row02_traceSegment_057_2538_0027, g32p_row02_traceSegment_057_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 2484 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2484 54 54, g32p_row02_traceSegment_057_2484_0054, g32p_row02_traceSegment_057_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 2376 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2376 108 108, g32p_row02_traceSegment_057_2376_0108, g32p_row02_traceSegment_057_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_057 2160 432 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2160 216 216, g32p_row02_traceSegment_057_2160_0216, g32p_row02_traceSegment_057_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_057 1728 864 = [0, 26] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1728 432 432, g32p_row02_traceSegment_057_1728_0432, g32p_row02_traceSegment_057_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2592 13 14, g32p_row02_traceSegment_057_2592_0013, g32p_row02_traceSegment_057_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2619 13 14, g32p_row02_traceSegment_057_2619_0013, g32p_row02_traceSegment_057_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2592 27 27, g32p_row02_traceSegment_057_2592_0027, g32p_row02_traceSegment_057_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2659 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2646 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2646 13 14, g32p_row02_traceSegment_057_2646_0013, g32p_row02_traceSegment_057_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2673 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2673 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2673 13 14, g32p_row02_traceSegment_057_2673_0013, g32p_row02_traceSegment_057_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2646 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2646 27 27, g32p_row02_traceSegment_057_2646_0027, g32p_row02_traceSegment_057_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 2592 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2592 54 54, g32p_row02_traceSegment_057_2592_0054, g32p_row02_traceSegment_057_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2700 13 14, g32p_row02_traceSegment_057_2700_0013, g32p_row02_traceSegment_057_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2740 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2727 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2727 13 14, g32p_row02_traceSegment_057_2727_0013, g32p_row02_traceSegment_057_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2700 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2700 27 27, g32p_row02_traceSegment_057_2700_0027, g32p_row02_traceSegment_057_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2754 13 14, g32p_row02_traceSegment_057_2754_0013, g32p_row02_traceSegment_057_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2781 13 14, g32p_row02_traceSegment_057_2781_0013, g32p_row02_traceSegment_057_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2754 27 27, g32p_row02_traceSegment_057_2754_0027, g32p_row02_traceSegment_057_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 2700 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2700 54 54, g32p_row02_traceSegment_057_2700_0054, g32p_row02_traceSegment_057_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 2592 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2592 108 108, g32p_row02_traceSegment_057_2592_0108, g32p_row02_traceSegment_057_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2808 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2821 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2808 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2808 13 14, g32p_row02_traceSegment_057_2808_0013, g32p_row02_traceSegment_057_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2835 13 14, g32p_row02_traceSegment_057_2835_0013, g32p_row02_traceSegment_057_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2808 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2808 27 27, g32p_row02_traceSegment_057_2808_0027, g32p_row02_traceSegment_057_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2862 13 14, g32p_row02_traceSegment_057_2862_0013, g32p_row02_traceSegment_057_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2889 13 14, g32p_row02_traceSegment_057_2889_0013, g32p_row02_traceSegment_057_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2862 27 27, g32p_row02_traceSegment_057_2862_0027, g32p_row02_traceSegment_057_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 2808 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2808 54 54, g32p_row02_traceSegment_057_2808_0054, g32p_row02_traceSegment_057_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2916 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2929 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2916 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2916 13 14, g32p_row02_traceSegment_057_2916_0013, g32p_row02_traceSegment_057_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2943 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2956 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2943 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2943 13 14, g32p_row02_traceSegment_057_2943_0013, g32p_row02_traceSegment_057_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2916 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2916 27 27, g32p_row02_traceSegment_057_2916_0027, g32p_row02_traceSegment_057_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2970 13 14, g32p_row02_traceSegment_057_2970_0013, g32p_row02_traceSegment_057_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2997 13 14, g32p_row02_traceSegment_057_2997_0013, g32p_row02_traceSegment_057_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2970 27 27, g32p_row02_traceSegment_057_2970_0027, g32p_row02_traceSegment_057_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 2916 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2916 54 54, g32p_row02_traceSegment_057_2916_0054, g32p_row02_traceSegment_057_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 2808 216 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2808 108 108, g32p_row02_traceSegment_057_2808_0108, g32p_row02_traceSegment_057_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_057 2592 432 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2592 216 216, g32p_row02_traceSegment_057_2592_0216, g32p_row02_traceSegment_057_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3024 13 14, g32p_row02_traceSegment_057_3024_0013, g32p_row02_traceSegment_057_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3051 13 14, g32p_row02_traceSegment_057_3051_0013, g32p_row02_traceSegment_057_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3024 27 27, g32p_row02_traceSegment_057_3024_0027, g32p_row02_traceSegment_057_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3078 13 14, g32p_row02_traceSegment_057_3078_0013, g32p_row02_traceSegment_057_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3105 13 14, g32p_row02_traceSegment_057_3105_0013, g32p_row02_traceSegment_057_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3078 27 27, g32p_row02_traceSegment_057_3078_0027, g32p_row02_traceSegment_057_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3024 54 54, g32p_row02_traceSegment_057_3024_0054, g32p_row02_traceSegment_057_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3132 13 14, g32p_row02_traceSegment_057_3132_0013, g32p_row02_traceSegment_057_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3159 13 14, g32p_row02_traceSegment_057_3159_0013, g32p_row02_traceSegment_057_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3132 27 27, g32p_row02_traceSegment_057_3132_0027, g32p_row02_traceSegment_057_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3199 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3186 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3186 13 14, g32p_row02_traceSegment_057_3186_0013, g32p_row02_traceSegment_057_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3213 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3213 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3213 13 14, g32p_row02_traceSegment_057_3213_0013, g32p_row02_traceSegment_057_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 3186 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3186 27 27, g32p_row02_traceSegment_057_3186_0027, g32p_row02_traceSegment_057_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 3132 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3132 54 54, g32p_row02_traceSegment_057_3132_0054, g32p_row02_traceSegment_057_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 3024 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3024 108 108, g32p_row02_traceSegment_057_3024_0108, g32p_row02_traceSegment_057_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3240 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3253 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3240 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3240 13 14, g32p_row02_traceSegment_057_3240_0013, g32p_row02_traceSegment_057_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3267 13 14, g32p_row02_traceSegment_057_3267_0013, g32p_row02_traceSegment_057_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 3240 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3240 27 27, g32p_row02_traceSegment_057_3240_0027, g32p_row02_traceSegment_057_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3294 13 = [0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3307 14 = [0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3294 27 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3294 13 14, g32p_row02_traceSegment_057_3294_0013, g32p_row02_traceSegment_057_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3321 13 = [0, 10] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3321 27 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3321 13 14, g32p_row02_traceSegment_057_3321_0013, g32p_row02_traceSegment_057_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 3294 54 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3294 27 27, g32p_row02_traceSegment_057_3294_0027, g32p_row02_traceSegment_057_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 3240 108 = [0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3240 54 54, g32p_row02_traceSegment_057_3240_0054, g32p_row02_traceSegment_057_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3361 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3348 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3348 13 14, g32p_row02_traceSegment_057_3348_0013, g32p_row02_traceSegment_057_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3375 13 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3388 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3375 27 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3375 13 14, g32p_row02_traceSegment_057_3375_0013, g32p_row02_traceSegment_057_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 3348 54 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3348 27 27, g32p_row02_traceSegment_057_3348_0027, g32p_row02_traceSegment_057_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3415 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3402 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3402 13 14, g32p_row02_traceSegment_057_3402_0013, g32p_row02_traceSegment_057_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_057 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_057 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_057_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_057 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3429 13 14, g32p_row02_traceSegment_057_3429_0013, g32p_row02_traceSegment_057_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_057 3402 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3402 27 27, g32p_row02_traceSegment_057_3402_0027, g32p_row02_traceSegment_057_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_057 3348 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3348 54 54, g32p_row02_traceSegment_057_3348_0054, g32p_row02_traceSegment_057_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_057 3240 216 = [0, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3240 108 108, g32p_row02_traceSegment_057_3240_0108, g32p_row02_traceSegment_057_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_057_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_057 3024 432 = [0, 36] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 3024 216 216, g32p_row02_traceSegment_057_3024_0216, g32p_row02_traceSegment_057_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_057_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_057 2592 864 = [0, 48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 2592 432 432, g32p_row02_traceSegment_057_2592_0432, g32p_row02_traceSegment_057_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_057_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_057 1728 1728 = [0, 74] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 1728 864 864, g32p_row02_traceSegment_057_1728_0864, g32p_row02_traceSegment_057_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_057_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_057 0 3456 = [0, 144] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_057 0 1728 1728, g32p_row02_traceSegment_057_0000_1728, g32p_row02_traceSegment_057_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_057 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 57 = [0, 144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_057_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_058 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 58 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_058_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 0 13 14, g32p_row02_traceSegment_058_0000_0013, g32p_row02_traceSegment_058_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 27 13 14, g32p_row02_traceSegment_058_0027_0013, g32p_row02_traceSegment_058_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 0 27 27, g32p_row02_traceSegment_058_0000_0027, g32p_row02_traceSegment_058_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 54 13 14, g32p_row02_traceSegment_058_0054_0013, g32p_row02_traceSegment_058_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 81 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 81 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 81 13 14, g32p_row02_traceSegment_058_0081_0013, g32p_row02_traceSegment_058_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 54 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 54 27 27, g32p_row02_traceSegment_058_0054_0027, g32p_row02_traceSegment_058_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 0 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 0 54 54, g32p_row02_traceSegment_058_0000_0054, g32p_row02_traceSegment_058_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 121 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 108 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 108 13 14, g32p_row02_traceSegment_058_0108_0013, g32p_row02_traceSegment_058_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 135 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 135 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 135 13 14, g32p_row02_traceSegment_058_0135_0013, g32p_row02_traceSegment_058_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 108 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 108 27 27, g32p_row02_traceSegment_058_0108_0027, g32p_row02_traceSegment_058_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 162 13 14, g32p_row02_traceSegment_058_0162_0013, g32p_row02_traceSegment_058_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 189 13 14, g32p_row02_traceSegment_058_0189_0013, g32p_row02_traceSegment_058_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 162 27 27, g32p_row02_traceSegment_058_0162_0027, g32p_row02_traceSegment_058_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 108 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 108 54 54, g32p_row02_traceSegment_058_0108_0054, g32p_row02_traceSegment_058_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 0 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 0 108 108, g32p_row02_traceSegment_058_0000_0108, g32p_row02_traceSegment_058_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 229 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 216 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 216 13 14, g32p_row02_traceSegment_058_0216_0013, g32p_row02_traceSegment_058_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 243 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 243 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 243 13 14, g32p_row02_traceSegment_058_0243_0013, g32p_row02_traceSegment_058_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 216 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 216 27 27, g32p_row02_traceSegment_058_0216_0027, g32p_row02_traceSegment_058_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 270 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 270 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 270 13 14, g32p_row02_traceSegment_058_0270_0013, g32p_row02_traceSegment_058_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 297 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 310 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 297 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 297 13 14, g32p_row02_traceSegment_058_0297_0013, g32p_row02_traceSegment_058_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 270 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 270 27 27, g32p_row02_traceSegment_058_0270_0027, g32p_row02_traceSegment_058_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 216 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 216 54 54, g32p_row02_traceSegment_058_0216_0054, g32p_row02_traceSegment_058_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 337 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 324 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 324 13 14, g32p_row02_traceSegment_058_0324_0013, g32p_row02_traceSegment_058_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 351 13 14, g32p_row02_traceSegment_058_0351_0013, g32p_row02_traceSegment_058_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 324 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 324 27 27, g32p_row02_traceSegment_058_0324_0027, g32p_row02_traceSegment_058_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 391 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 378 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 378 13 14, g32p_row02_traceSegment_058_0378_0013, g32p_row02_traceSegment_058_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 405 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 405 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 405 13 14, g32p_row02_traceSegment_058_0405_0013, g32p_row02_traceSegment_058_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 378 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 378 27 27, g32p_row02_traceSegment_058_0378_0027, g32p_row02_traceSegment_058_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 324 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 324 54 54, g32p_row02_traceSegment_058_0324_0054, g32p_row02_traceSegment_058_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 216 216 = [9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 216 108 108, g32p_row02_traceSegment_058_0216_0108, g32p_row02_traceSegment_058_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_058 0 432 = [13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 0 216 216, g32p_row02_traceSegment_058_0000_0216, g32p_row02_traceSegment_058_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 432 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 432 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 432 13 14, g32p_row02_traceSegment_058_0432_0013, g32p_row02_traceSegment_058_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 459 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 472 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 459 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 459 13 14, g32p_row02_traceSegment_058_0459_0013, g32p_row02_traceSegment_058_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 432 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 432 27 27, g32p_row02_traceSegment_058_0432_0027, g32p_row02_traceSegment_058_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 486 13 14, g32p_row02_traceSegment_058_0486_0013, g32p_row02_traceSegment_058_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 526 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 513 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 513 13 14, g32p_row02_traceSegment_058_0513_0013, g32p_row02_traceSegment_058_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 486 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 486 27 27, g32p_row02_traceSegment_058_0486_0027, g32p_row02_traceSegment_058_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 432 108 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 432 54 54, g32p_row02_traceSegment_058_0432_0054, g32p_row02_traceSegment_058_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 540 13 14, g32p_row02_traceSegment_058_0540_0013, g32p_row02_traceSegment_058_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 580 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 567 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 567 13 14, g32p_row02_traceSegment_058_0567_0013, g32p_row02_traceSegment_058_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 540 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 540 27 27, g32p_row02_traceSegment_058_0540_0027, g32p_row02_traceSegment_058_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 594 13 14, g32p_row02_traceSegment_058_0594_0013, g32p_row02_traceSegment_058_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 621 13 14, g32p_row02_traceSegment_058_0621_0013, g32p_row02_traceSegment_058_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 594 27 27, g32p_row02_traceSegment_058_0594_0027, g32p_row02_traceSegment_058_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 540 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 540 54 54, g32p_row02_traceSegment_058_0540_0054, g32p_row02_traceSegment_058_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 432 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 432 108 108, g32p_row02_traceSegment_058_0432_0108, g32p_row02_traceSegment_058_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 648 13 14, g32p_row02_traceSegment_058_0648_0013, g32p_row02_traceSegment_058_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 675 13 14, g32p_row02_traceSegment_058_0675_0013, g32p_row02_traceSegment_058_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 648 27 27, g32p_row02_traceSegment_058_0648_0027, g32p_row02_traceSegment_058_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 702 13 14, g32p_row02_traceSegment_058_0702_0013, g32p_row02_traceSegment_058_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 729 13 14, g32p_row02_traceSegment_058_0729_0013, g32p_row02_traceSegment_058_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 702 27 27, g32p_row02_traceSegment_058_0702_0027, g32p_row02_traceSegment_058_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 648 54 54, g32p_row02_traceSegment_058_0648_0054, g32p_row02_traceSegment_058_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 756 13 14, g32p_row02_traceSegment_058_0756_0013, g32p_row02_traceSegment_058_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 783 13 14, g32p_row02_traceSegment_058_0783_0013, g32p_row02_traceSegment_058_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 756 27 27, g32p_row02_traceSegment_058_0756_0027, g32p_row02_traceSegment_058_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 810 13 14, g32p_row02_traceSegment_058_0810_0013, g32p_row02_traceSegment_058_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 837 13 14, g32p_row02_traceSegment_058_0837_0013, g32p_row02_traceSegment_058_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 810 27 27, g32p_row02_traceSegment_058_0810_0027, g32p_row02_traceSegment_058_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 756 54 54, g32p_row02_traceSegment_058_0756_0054, g32p_row02_traceSegment_058_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 648 108 108, g32p_row02_traceSegment_058_0648_0108, g32p_row02_traceSegment_058_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_058 432 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 432 216 216, g32p_row02_traceSegment_058_0432_0216, g32p_row02_traceSegment_058_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_058 0 864 = [19] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 0 432 432, g32p_row02_traceSegment_058_0000_0432, g32p_row02_traceSegment_058_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 864 13 14, g32p_row02_traceSegment_058_0864_0013, g32p_row02_traceSegment_058_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 891 13 14, g32p_row02_traceSegment_058_0891_0013, g32p_row02_traceSegment_058_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 864 27 27, g32p_row02_traceSegment_058_0864_0027, g32p_row02_traceSegment_058_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 918 13 14, g32p_row02_traceSegment_058_0918_0013, g32p_row02_traceSegment_058_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 945 13 14, g32p_row02_traceSegment_058_0945_0013, g32p_row02_traceSegment_058_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 918 27 27, g32p_row02_traceSegment_058_0918_0027, g32p_row02_traceSegment_058_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 864 54 54, g32p_row02_traceSegment_058_0864_0054, g32p_row02_traceSegment_058_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 972 13 14, g32p_row02_traceSegment_058_0972_0013, g32p_row02_traceSegment_058_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 999 13 14, g32p_row02_traceSegment_058_0999_0013, g32p_row02_traceSegment_058_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 972 27 27, g32p_row02_traceSegment_058_0972_0027, g32p_row02_traceSegment_058_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1026 13 14, g32p_row02_traceSegment_058_1026_0013, g32p_row02_traceSegment_058_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1053 13 14, g32p_row02_traceSegment_058_1053_0013, g32p_row02_traceSegment_058_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1026 27 27, g32p_row02_traceSegment_058_1026_0027, g32p_row02_traceSegment_058_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 972 54 54, g32p_row02_traceSegment_058_0972_0054, g32p_row02_traceSegment_058_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 864 108 108, g32p_row02_traceSegment_058_0864_0108, g32p_row02_traceSegment_058_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1093 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1080 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1080 13 14, g32p_row02_traceSegment_058_1080_0013, g32p_row02_traceSegment_058_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1107 13 14, g32p_row02_traceSegment_058_1107_0013, g32p_row02_traceSegment_058_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1080 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1080 27 27, g32p_row02_traceSegment_058_1080_0027, g32p_row02_traceSegment_058_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1134 13 14, g32p_row02_traceSegment_058_1134_0013, g32p_row02_traceSegment_058_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1161 13 14, g32p_row02_traceSegment_058_1161_0013, g32p_row02_traceSegment_058_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1134 27 27, g32p_row02_traceSegment_058_1134_0027, g32p_row02_traceSegment_058_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 1080 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1080 54 54, g32p_row02_traceSegment_058_1080_0054, g32p_row02_traceSegment_058_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1201 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1188 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1188 13 14, g32p_row02_traceSegment_058_1188_0013, g32p_row02_traceSegment_058_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1215 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1215 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1215 13 14, g32p_row02_traceSegment_058_1215_0013, g32p_row02_traceSegment_058_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1188 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1188 27 27, g32p_row02_traceSegment_058_1188_0027, g32p_row02_traceSegment_058_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1242 13 14, g32p_row02_traceSegment_058_1242_0013, g32p_row02_traceSegment_058_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1269 13 14, g32p_row02_traceSegment_058_1269_0013, g32p_row02_traceSegment_058_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1242 27 27, g32p_row02_traceSegment_058_1242_0027, g32p_row02_traceSegment_058_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 1188 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1188 54 54, g32p_row02_traceSegment_058_1188_0054, g32p_row02_traceSegment_058_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 1080 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1080 108 108, g32p_row02_traceSegment_058_1080_0108, g32p_row02_traceSegment_058_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_058 864 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 864 216 216, g32p_row02_traceSegment_058_0864_0216, g32p_row02_traceSegment_058_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1296 13 14, g32p_row02_traceSegment_058_1296_0013, g32p_row02_traceSegment_058_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1323 13 14, g32p_row02_traceSegment_058_1323_0013, g32p_row02_traceSegment_058_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1296 27 27, g32p_row02_traceSegment_058_1296_0027, g32p_row02_traceSegment_058_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1350 13 14, g32p_row02_traceSegment_058_1350_0013, g32p_row02_traceSegment_058_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1377 13 14, g32p_row02_traceSegment_058_1377_0013, g32p_row02_traceSegment_058_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1350 27 27, g32p_row02_traceSegment_058_1350_0027, g32p_row02_traceSegment_058_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1296 54 54, g32p_row02_traceSegment_058_1296_0054, g32p_row02_traceSegment_058_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1404 13 14, g32p_row02_traceSegment_058_1404_0013, g32p_row02_traceSegment_058_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1431 13 14, g32p_row02_traceSegment_058_1431_0013, g32p_row02_traceSegment_058_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1404 27 27, g32p_row02_traceSegment_058_1404_0027, g32p_row02_traceSegment_058_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1458 13 14, g32p_row02_traceSegment_058_1458_0013, g32p_row02_traceSegment_058_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1485 13 14, g32p_row02_traceSegment_058_1485_0013, g32p_row02_traceSegment_058_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1458 27 27, g32p_row02_traceSegment_058_1458_0027, g32p_row02_traceSegment_058_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1404 54 54, g32p_row02_traceSegment_058_1404_0054, g32p_row02_traceSegment_058_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1296 108 108, g32p_row02_traceSegment_058_1296_0108, g32p_row02_traceSegment_058_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1525 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1512 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1512 13 14, g32p_row02_traceSegment_058_1512_0013, g32p_row02_traceSegment_058_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1539 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1539 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1539 13 14, g32p_row02_traceSegment_058_1539_0013, g32p_row02_traceSegment_058_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1512 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1512 27 27, g32p_row02_traceSegment_058_1512_0027, g32p_row02_traceSegment_058_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1566 13 14, g32p_row02_traceSegment_058_1566_0013, g32p_row02_traceSegment_058_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1593 13 14, g32p_row02_traceSegment_058_1593_0013, g32p_row02_traceSegment_058_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1566 27 27, g32p_row02_traceSegment_058_1566_0027, g32p_row02_traceSegment_058_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 1512 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1512 54 54, g32p_row02_traceSegment_058_1512_0054, g32p_row02_traceSegment_058_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1620 13 14, g32p_row02_traceSegment_058_1620_0013, g32p_row02_traceSegment_058_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1647 13 14, g32p_row02_traceSegment_058_1647_0013, g32p_row02_traceSegment_058_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1620 27 27, g32p_row02_traceSegment_058_1620_0027, g32p_row02_traceSegment_058_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1674 13 14, g32p_row02_traceSegment_058_1674_0013, g32p_row02_traceSegment_058_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1701 13 14, g32p_row02_traceSegment_058_1701_0013, g32p_row02_traceSegment_058_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1674 27 27, g32p_row02_traceSegment_058_1674_0027, g32p_row02_traceSegment_058_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1620 54 54, g32p_row02_traceSegment_058_1620_0054, g32p_row02_traceSegment_058_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 1512 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1512 108 108, g32p_row02_traceSegment_058_1512_0108, g32p_row02_traceSegment_058_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_058 1296 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1296 216 216, g32p_row02_traceSegment_058_1296_0216, g32p_row02_traceSegment_058_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_058 864 864 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 864 432 432, g32p_row02_traceSegment_058_0864_0432, g32p_row02_traceSegment_058_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_058 0 1728 = [24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 0 864 864, g32p_row02_traceSegment_058_0000_0864, g32p_row02_traceSegment_058_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1728 13 14, g32p_row02_traceSegment_058_1728_0013, g32p_row02_traceSegment_058_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1755 13 14, g32p_row02_traceSegment_058_1755_0013, g32p_row02_traceSegment_058_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1728 27 27, g32p_row02_traceSegment_058_1728_0027, g32p_row02_traceSegment_058_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1782 13 14, g32p_row02_traceSegment_058_1782_0013, g32p_row02_traceSegment_058_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1809 13 14, g32p_row02_traceSegment_058_1809_0013, g32p_row02_traceSegment_058_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1782 27 27, g32p_row02_traceSegment_058_1782_0027, g32p_row02_traceSegment_058_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1728 54 54, g32p_row02_traceSegment_058_1728_0054, g32p_row02_traceSegment_058_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1836 13 14, g32p_row02_traceSegment_058_1836_0013, g32p_row02_traceSegment_058_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1863 13 14, g32p_row02_traceSegment_058_1863_0013, g32p_row02_traceSegment_058_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1836 27 27, g32p_row02_traceSegment_058_1836_0027, g32p_row02_traceSegment_058_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1890 13 14, g32p_row02_traceSegment_058_1890_0013, g32p_row02_traceSegment_058_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1917 13 14, g32p_row02_traceSegment_058_1917_0013, g32p_row02_traceSegment_058_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1890 27 27, g32p_row02_traceSegment_058_1890_0027, g32p_row02_traceSegment_058_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1836 54 54, g32p_row02_traceSegment_058_1836_0054, g32p_row02_traceSegment_058_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1728 108 108, g32p_row02_traceSegment_058_1728_0108, g32p_row02_traceSegment_058_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1944 13 14, g32p_row02_traceSegment_058_1944_0013, g32p_row02_traceSegment_058_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1971 13 14, g32p_row02_traceSegment_058_1971_0013, g32p_row02_traceSegment_058_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1944 27 27, g32p_row02_traceSegment_058_1944_0027, g32p_row02_traceSegment_058_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 1998 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 1998 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1998 13 14, g32p_row02_traceSegment_058_1998_0013, g32p_row02_traceSegment_058_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2038 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2025 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2025 13 14, g32p_row02_traceSegment_058_2025_0013, g32p_row02_traceSegment_058_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 1998 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1998 27 27, g32p_row02_traceSegment_058_1998_0027, g32p_row02_traceSegment_058_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 1944 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1944 54 54, g32p_row02_traceSegment_058_1944_0054, g32p_row02_traceSegment_058_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2052 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2052 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2052 13 14, g32p_row02_traceSegment_058_2052_0013, g32p_row02_traceSegment_058_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2079 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2079 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2079 13 14, g32p_row02_traceSegment_058_2079_0013, g32p_row02_traceSegment_058_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2052 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2052 27 27, g32p_row02_traceSegment_058_2052_0027, g32p_row02_traceSegment_058_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2106 13 14, g32p_row02_traceSegment_058_2106_0013, g32p_row02_traceSegment_058_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2133 13 14, g32p_row02_traceSegment_058_2133_0013, g32p_row02_traceSegment_058_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2106 27 27, g32p_row02_traceSegment_058_2106_0027, g32p_row02_traceSegment_058_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 2052 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2052 54 54, g32p_row02_traceSegment_058_2052_0054, g32p_row02_traceSegment_058_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 1944 216 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1944 108 108, g32p_row02_traceSegment_058_1944_0108, g32p_row02_traceSegment_058_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_058 1728 432 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1728 216 216, g32p_row02_traceSegment_058_1728_0216, g32p_row02_traceSegment_058_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2173 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2160 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2160 13 14, g32p_row02_traceSegment_058_2160_0013, g32p_row02_traceSegment_058_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2187 13 14, g32p_row02_traceSegment_058_2187_0013, g32p_row02_traceSegment_058_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2160 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2160 27 27, g32p_row02_traceSegment_058_2160_0027, g32p_row02_traceSegment_058_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2227 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2214 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2214 13 14, g32p_row02_traceSegment_058_2214_0013, g32p_row02_traceSegment_058_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2254 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2241 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2241 13 14, g32p_row02_traceSegment_058_2241_0013, g32p_row02_traceSegment_058_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2214 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2214 27 27, g32p_row02_traceSegment_058_2214_0027, g32p_row02_traceSegment_058_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 2160 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2160 54 54, g32p_row02_traceSegment_058_2160_0054, g32p_row02_traceSegment_058_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2268 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2268 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2268 13 14, g32p_row02_traceSegment_058_2268_0013, g32p_row02_traceSegment_058_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2295 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2295 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2295 13 14, g32p_row02_traceSegment_058_2295_0013, g32p_row02_traceSegment_058_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2268 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2268 27 27, g32p_row02_traceSegment_058_2268_0027, g32p_row02_traceSegment_058_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2322 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2322 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2322 13 14, g32p_row02_traceSegment_058_2322_0013, g32p_row02_traceSegment_058_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2349 13 14, g32p_row02_traceSegment_058_2349_0013, g32p_row02_traceSegment_058_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2322 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2322 27 27, g32p_row02_traceSegment_058_2322_0027, g32p_row02_traceSegment_058_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 2268 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2268 54 54, g32p_row02_traceSegment_058_2268_0054, g32p_row02_traceSegment_058_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 2160 216 = [7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2160 108 108, g32p_row02_traceSegment_058_2160_0108, g32p_row02_traceSegment_058_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2376 13 14, g32p_row02_traceSegment_058_2376_0013, g32p_row02_traceSegment_058_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2403 13 14, g32p_row02_traceSegment_058_2403_0013, g32p_row02_traceSegment_058_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2376 27 27, g32p_row02_traceSegment_058_2376_0027, g32p_row02_traceSegment_058_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2430 13 14, g32p_row02_traceSegment_058_2430_0013, g32p_row02_traceSegment_058_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2470 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2457 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2457 13 14, g32p_row02_traceSegment_058_2457_0013, g32p_row02_traceSegment_058_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2430 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2430 27 27, g32p_row02_traceSegment_058_2430_0027, g32p_row02_traceSegment_058_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 2376 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2376 54 54, g32p_row02_traceSegment_058_2376_0054, g32p_row02_traceSegment_058_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2484 13 14, g32p_row02_traceSegment_058_2484_0013, g32p_row02_traceSegment_058_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2511 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2511 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2511 13 14, g32p_row02_traceSegment_058_2511_0013, g32p_row02_traceSegment_058_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2484 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2484 27 27, g32p_row02_traceSegment_058_2484_0027, g32p_row02_traceSegment_058_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2538 13 14, g32p_row02_traceSegment_058_2538_0013, g32p_row02_traceSegment_058_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2565 13 14, g32p_row02_traceSegment_058_2565_0013, g32p_row02_traceSegment_058_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2538 27 27, g32p_row02_traceSegment_058_2538_0027, g32p_row02_traceSegment_058_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 2484 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2484 54 54, g32p_row02_traceSegment_058_2484_0054, g32p_row02_traceSegment_058_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 2376 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2376 108 108, g32p_row02_traceSegment_058_2376_0108, g32p_row02_traceSegment_058_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_058 2160 432 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2160 216 216, g32p_row02_traceSegment_058_2160_0216, g32p_row02_traceSegment_058_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_058 1728 864 = [15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1728 432 432, g32p_row02_traceSegment_058_1728_0432, g32p_row02_traceSegment_058_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2592 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2592 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2592 13 14, g32p_row02_traceSegment_058_2592_0013, g32p_row02_traceSegment_058_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2619 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2619 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2619 13 14, g32p_row02_traceSegment_058_2619_0013, g32p_row02_traceSegment_058_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2592 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2592 27 27, g32p_row02_traceSegment_058_2592_0027, g32p_row02_traceSegment_058_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2659 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2646 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2646 13 14, g32p_row02_traceSegment_058_2646_0013, g32p_row02_traceSegment_058_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2686 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2673 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2673 13 14, g32p_row02_traceSegment_058_2673_0013, g32p_row02_traceSegment_058_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2646 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2646 27 27, g32p_row02_traceSegment_058_2646_0027, g32p_row02_traceSegment_058_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 2592 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2592 54 54, g32p_row02_traceSegment_058_2592_0054, g32p_row02_traceSegment_058_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2700 13 14, g32p_row02_traceSegment_058_2700_0013, g32p_row02_traceSegment_058_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2727 13 14, g32p_row02_traceSegment_058_2727_0013, g32p_row02_traceSegment_058_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2700 27 27, g32p_row02_traceSegment_058_2700_0027, g32p_row02_traceSegment_058_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2754 13 14, g32p_row02_traceSegment_058_2754_0013, g32p_row02_traceSegment_058_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2781 13 14, g32p_row02_traceSegment_058_2781_0013, g32p_row02_traceSegment_058_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2754 27 27, g32p_row02_traceSegment_058_2754_0027, g32p_row02_traceSegment_058_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2700 54 54, g32p_row02_traceSegment_058_2700_0054, g32p_row02_traceSegment_058_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 2592 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2592 108 108, g32p_row02_traceSegment_058_2592_0108, g32p_row02_traceSegment_058_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2808 13 14, g32p_row02_traceSegment_058_2808_0013, g32p_row02_traceSegment_058_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2835 13 14, g32p_row02_traceSegment_058_2835_0013, g32p_row02_traceSegment_058_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2808 27 27, g32p_row02_traceSegment_058_2808_0027, g32p_row02_traceSegment_058_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2862 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2862 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2862 13 14, g32p_row02_traceSegment_058_2862_0013, g32p_row02_traceSegment_058_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2889 13 14, g32p_row02_traceSegment_058_2889_0013, g32p_row02_traceSegment_058_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2862 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2862 27 27, g32p_row02_traceSegment_058_2862_0027, g32p_row02_traceSegment_058_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 2808 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2808 54 54, g32p_row02_traceSegment_058_2808_0054, g32p_row02_traceSegment_058_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2916 13 14, g32p_row02_traceSegment_058_2916_0013, g32p_row02_traceSegment_058_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2943 13 14, g32p_row02_traceSegment_058_2943_0013, g32p_row02_traceSegment_058_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2916 27 27, g32p_row02_traceSegment_058_2916_0027, g32p_row02_traceSegment_058_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2970 13 14, g32p_row02_traceSegment_058_2970_0013, g32p_row02_traceSegment_058_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 2997 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 2997 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2997 13 14, g32p_row02_traceSegment_058_2997_0013, g32p_row02_traceSegment_058_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 2970 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2970 27 27, g32p_row02_traceSegment_058_2970_0027, g32p_row02_traceSegment_058_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 2916 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2916 54 54, g32p_row02_traceSegment_058_2916_0054, g32p_row02_traceSegment_058_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 2808 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2808 108 108, g32p_row02_traceSegment_058_2808_0108, g32p_row02_traceSegment_058_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_058 2592 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2592 216 216, g32p_row02_traceSegment_058_2592_0216, g32p_row02_traceSegment_058_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3024 13 14, g32p_row02_traceSegment_058_3024_0013, g32p_row02_traceSegment_058_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3051 13 14, g32p_row02_traceSegment_058_3051_0013, g32p_row02_traceSegment_058_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3024 27 27, g32p_row02_traceSegment_058_3024_0027, g32p_row02_traceSegment_058_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3078 13 14, g32p_row02_traceSegment_058_3078_0013, g32p_row02_traceSegment_058_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3105 13 14, g32p_row02_traceSegment_058_3105_0013, g32p_row02_traceSegment_058_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3078 27 27, g32p_row02_traceSegment_058_3078_0027, g32p_row02_traceSegment_058_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3024 54 54, g32p_row02_traceSegment_058_3024_0054, g32p_row02_traceSegment_058_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3132 13 14, g32p_row02_traceSegment_058_3132_0013, g32p_row02_traceSegment_058_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3159 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3172 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3159 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3159 13 14, g32p_row02_traceSegment_058_3159_0013, g32p_row02_traceSegment_058_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 3132 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3132 27 27, g32p_row02_traceSegment_058_3132_0027, g32p_row02_traceSegment_058_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3186 13 14, g32p_row02_traceSegment_058_3186_0013, g32p_row02_traceSegment_058_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3213 13 14, g32p_row02_traceSegment_058_3213_0013, g32p_row02_traceSegment_058_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3186 27 27, g32p_row02_traceSegment_058_3186_0027, g32p_row02_traceSegment_058_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 3132 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3132 54 54, g32p_row02_traceSegment_058_3132_0054, g32p_row02_traceSegment_058_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 3024 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3024 108 108, g32p_row02_traceSegment_058_3024_0108, g32p_row02_traceSegment_058_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3240 13 14, g32p_row02_traceSegment_058_3240_0013, g32p_row02_traceSegment_058_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3267 13 14, g32p_row02_traceSegment_058_3267_0013, g32p_row02_traceSegment_058_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3240 27 27, g32p_row02_traceSegment_058_3240_0027, g32p_row02_traceSegment_058_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3294 13 14, g32p_row02_traceSegment_058_3294_0013, g32p_row02_traceSegment_058_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3321 13 14, g32p_row02_traceSegment_058_3321_0013, g32p_row02_traceSegment_058_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3294 27 27, g32p_row02_traceSegment_058_3294_0027, g32p_row02_traceSegment_058_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3240 54 54, g32p_row02_traceSegment_058_3240_0054, g32p_row02_traceSegment_058_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3348 13 14, g32p_row02_traceSegment_058_3348_0013, g32p_row02_traceSegment_058_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3375 13 14, g32p_row02_traceSegment_058_3375_0013, g32p_row02_traceSegment_058_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3348 27 27, g32p_row02_traceSegment_058_3348_0027, g32p_row02_traceSegment_058_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3402 13 14, g32p_row02_traceSegment_058_3402_0013, g32p_row02_traceSegment_058_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_058 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_058 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_058_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_058 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3429 13 14, g32p_row02_traceSegment_058_3429_0013, g32p_row02_traceSegment_058_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_058 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3402 27 27, g32p_row02_traceSegment_058_3402_0027, g32p_row02_traceSegment_058_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_058 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3348 54 54, g32p_row02_traceSegment_058_3348_0054, g32p_row02_traceSegment_058_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_058 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3240 108 108, g32p_row02_traceSegment_058_3240_0108, g32p_row02_traceSegment_058_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_058_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_058 3024 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 3024 216 216, g32p_row02_traceSegment_058_3024_0216, g32p_row02_traceSegment_058_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_058_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_058 2592 864 = [9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 2592 432 432, g32p_row02_traceSegment_058_2592_0432, g32p_row02_traceSegment_058_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_058_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_058 1728 1728 = [24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 1728 864 864, g32p_row02_traceSegment_058_1728_0864, g32p_row02_traceSegment_058_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_058_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_058 0 3456 = [48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_058 0 1728 1728, g32p_row02_traceSegment_058_0000_1728, g32p_row02_traceSegment_058_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_058 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 58 = [48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_058_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_059 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 59 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_059_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 0 13 14, g32p_row02_traceSegment_059_0000_0013, g32p_row02_traceSegment_059_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 27 13 14, g32p_row02_traceSegment_059_0027_0013, g32p_row02_traceSegment_059_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 0 27 27, g32p_row02_traceSegment_059_0000_0027, g32p_row02_traceSegment_059_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 54 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 54 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 54 13 14, g32p_row02_traceSegment_059_0054_0013, g32p_row02_traceSegment_059_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 81 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 81 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 81 13 14, g32p_row02_traceSegment_059_0081_0013, g32p_row02_traceSegment_059_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 54 54 = [1, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 54 27 27, g32p_row02_traceSegment_059_0054_0027, g32p_row02_traceSegment_059_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 0 108 = [1, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 0 54 54, g32p_row02_traceSegment_059_0000_0054, g32p_row02_traceSegment_059_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 108 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 108 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 108 13 14, g32p_row02_traceSegment_059_0108_0013, g32p_row02_traceSegment_059_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 135 13 14, g32p_row02_traceSegment_059_0135_0013, g32p_row02_traceSegment_059_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 108 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 108 27 27, g32p_row02_traceSegment_059_0108_0027, g32p_row02_traceSegment_059_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 162 13 14, g32p_row02_traceSegment_059_0162_0013, g32p_row02_traceSegment_059_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 202 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 189 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 189 13 14, g32p_row02_traceSegment_059_0189_0013, g32p_row02_traceSegment_059_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 162 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 162 27 27, g32p_row02_traceSegment_059_0162_0027, g32p_row02_traceSegment_059_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 108 108 = [1, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 108 54 54, g32p_row02_traceSegment_059_0108_0054, g32p_row02_traceSegment_059_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 0 216 = [2, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 0 108 108, g32p_row02_traceSegment_059_0000_0108, g32p_row02_traceSegment_059_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 216 13 14, g32p_row02_traceSegment_059_0216_0013, g32p_row02_traceSegment_059_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 243 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 256 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 243 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 243 13 14, g32p_row02_traceSegment_059_0243_0013, g32p_row02_traceSegment_059_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 216 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 216 27 27, g32p_row02_traceSegment_059_0216_0027, g32p_row02_traceSegment_059_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 270 13 14, g32p_row02_traceSegment_059_0270_0013, g32p_row02_traceSegment_059_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 297 13 14, g32p_row02_traceSegment_059_0297_0013, g32p_row02_traceSegment_059_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 270 27 27, g32p_row02_traceSegment_059_0270_0027, g32p_row02_traceSegment_059_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 216 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 216 54 54, g32p_row02_traceSegment_059_0216_0054, g32p_row02_traceSegment_059_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 337 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 324 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 324 13 14, g32p_row02_traceSegment_059_0324_0013, g32p_row02_traceSegment_059_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 351 13 14, g32p_row02_traceSegment_059_0351_0013, g32p_row02_traceSegment_059_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 324 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 324 27 27, g32p_row02_traceSegment_059_0324_0027, g32p_row02_traceSegment_059_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 378 13 14, g32p_row02_traceSegment_059_0378_0013, g32p_row02_traceSegment_059_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 418 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 405 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 405 13 14, g32p_row02_traceSegment_059_0405_0013, g32p_row02_traceSegment_059_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 378 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 378 27 27, g32p_row02_traceSegment_059_0378_0027, g32p_row02_traceSegment_059_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 324 108 = [1, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 324 54 54, g32p_row02_traceSegment_059_0324_0054, g32p_row02_traceSegment_059_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 216 216 = [1, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 216 108 108, g32p_row02_traceSegment_059_0216_0108, g32p_row02_traceSegment_059_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_059 0 432 = [3, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 0 216 216, g32p_row02_traceSegment_059_0000_0216, g32p_row02_traceSegment_059_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 432 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 432 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 432 13 14, g32p_row02_traceSegment_059_0432_0013, g32p_row02_traceSegment_059_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 459 13 14, g32p_row02_traceSegment_059_0459_0013, g32p_row02_traceSegment_059_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 432 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 432 27 27, g32p_row02_traceSegment_059_0432_0027, g32p_row02_traceSegment_059_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 486 13 14, g32p_row02_traceSegment_059_0486_0013, g32p_row02_traceSegment_059_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 513 13 14, g32p_row02_traceSegment_059_0513_0013, g32p_row02_traceSegment_059_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 486 27 27, g32p_row02_traceSegment_059_0486_0027, g32p_row02_traceSegment_059_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 432 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 432 54 54, g32p_row02_traceSegment_059_0432_0054, g32p_row02_traceSegment_059_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 540 13 14, g32p_row02_traceSegment_059_0540_0013, g32p_row02_traceSegment_059_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 567 13 14, g32p_row02_traceSegment_059_0567_0013, g32p_row02_traceSegment_059_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 540 27 27, g32p_row02_traceSegment_059_0540_0027, g32p_row02_traceSegment_059_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 594 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 594 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 594 13 14, g32p_row02_traceSegment_059_0594_0013, g32p_row02_traceSegment_059_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 621 13 14, g32p_row02_traceSegment_059_0621_0013, g32p_row02_traceSegment_059_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 594 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 594 27 27, g32p_row02_traceSegment_059_0594_0027, g32p_row02_traceSegment_059_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 540 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 540 54 54, g32p_row02_traceSegment_059_0540_0054, g32p_row02_traceSegment_059_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 432 216 = [1, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 432 108 108, g32p_row02_traceSegment_059_0432_0108, g32p_row02_traceSegment_059_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 648 13 14, g32p_row02_traceSegment_059_0648_0013, g32p_row02_traceSegment_059_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 675 13 14, g32p_row02_traceSegment_059_0675_0013, g32p_row02_traceSegment_059_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 648 27 27, g32p_row02_traceSegment_059_0648_0027, g32p_row02_traceSegment_059_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 702 13 14, g32p_row02_traceSegment_059_0702_0013, g32p_row02_traceSegment_059_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 729 13 14, g32p_row02_traceSegment_059_0729_0013, g32p_row02_traceSegment_059_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 702 27 27, g32p_row02_traceSegment_059_0702_0027, g32p_row02_traceSegment_059_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 648 54 54, g32p_row02_traceSegment_059_0648_0054, g32p_row02_traceSegment_059_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 769 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 756 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 756 13 14, g32p_row02_traceSegment_059_0756_0013, g32p_row02_traceSegment_059_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 783 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 796 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 783 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 783 13 14, g32p_row02_traceSegment_059_0783_0013, g32p_row02_traceSegment_059_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 756 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 756 27 27, g32p_row02_traceSegment_059_0756_0027, g32p_row02_traceSegment_059_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 810 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 823 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 810 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 810 13 14, g32p_row02_traceSegment_059_0810_0013, g32p_row02_traceSegment_059_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 850 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 837 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 837 13 14, g32p_row02_traceSegment_059_0837_0013, g32p_row02_traceSegment_059_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 810 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 810 27 27, g32p_row02_traceSegment_059_0810_0027, g32p_row02_traceSegment_059_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 756 108 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 756 54 54, g32p_row02_traceSegment_059_0756_0054, g32p_row02_traceSegment_059_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 648 216 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 648 108 108, g32p_row02_traceSegment_059_0648_0108, g32p_row02_traceSegment_059_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_059 432 432 = [9, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 432 216 216, g32p_row02_traceSegment_059_0432_0216, g32p_row02_traceSegment_059_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_059 0 864 = [12, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 0 432 432, g32p_row02_traceSegment_059_0000_0432, g32p_row02_traceSegment_059_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 864 13 14, g32p_row02_traceSegment_059_0864_0013, g32p_row02_traceSegment_059_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 891 13 14, g32p_row02_traceSegment_059_0891_0013, g32p_row02_traceSegment_059_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 864 27 27, g32p_row02_traceSegment_059_0864_0027, g32p_row02_traceSegment_059_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 931 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 918 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 918 13 14, g32p_row02_traceSegment_059_0918_0013, g32p_row02_traceSegment_059_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 945 13 14, g32p_row02_traceSegment_059_0945_0013, g32p_row02_traceSegment_059_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 918 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 918 27 27, g32p_row02_traceSegment_059_0918_0027, g32p_row02_traceSegment_059_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 864 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 864 54 54, g32p_row02_traceSegment_059_0864_0054, g32p_row02_traceSegment_059_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 972 13 14, g32p_row02_traceSegment_059_0972_0013, g32p_row02_traceSegment_059_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 999 13 14, g32p_row02_traceSegment_059_0999_0013, g32p_row02_traceSegment_059_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 972 27 27, g32p_row02_traceSegment_059_0972_0027, g32p_row02_traceSegment_059_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1026 13 14, g32p_row02_traceSegment_059_1026_0013, g32p_row02_traceSegment_059_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1066 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1053 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1053 13 14, g32p_row02_traceSegment_059_1053_0013, g32p_row02_traceSegment_059_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1026 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1026 27 27, g32p_row02_traceSegment_059_1026_0027, g32p_row02_traceSegment_059_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 972 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 972 54 54, g32p_row02_traceSegment_059_0972_0054, g32p_row02_traceSegment_059_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 864 216 = [1, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 864 108 108, g32p_row02_traceSegment_059_0864_0108, g32p_row02_traceSegment_059_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1080 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1093 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1080 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1080 13 14, g32p_row02_traceSegment_059_1080_0013, g32p_row02_traceSegment_059_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1107 13 14, g32p_row02_traceSegment_059_1107_0013, g32p_row02_traceSegment_059_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1080 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1080 27 27, g32p_row02_traceSegment_059_1080_0027, g32p_row02_traceSegment_059_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1134 13 = [1, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1147 14 = [0, 0, 0, 0, 0, 7] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1134 27 = [1, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1134 13 14, g32p_row02_traceSegment_059_1134_0013, g32p_row02_traceSegment_059_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1161 13 = [0, 0, 0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1174 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1161 27 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1161 13 14, g32p_row02_traceSegment_059_1161_0013, g32p_row02_traceSegment_059_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1134 54 = [1, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1134 27 27, g32p_row02_traceSegment_059_1134_0027, g32p_row02_traceSegment_059_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 1080 108 = [4, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1080 54 54, g32p_row02_traceSegment_059_1080_0054, g32p_row02_traceSegment_059_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1188 13 14, g32p_row02_traceSegment_059_1188_0013, g32p_row02_traceSegment_059_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1215 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1228 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1215 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1215 13 14, g32p_row02_traceSegment_059_1215_0013, g32p_row02_traceSegment_059_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1188 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1188 27 27, g32p_row02_traceSegment_059_1188_0027, g32p_row02_traceSegment_059_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1242 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1242 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1242 13 14, g32p_row02_traceSegment_059_1242_0013, g32p_row02_traceSegment_059_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1269 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1282 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1269 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1269 13 14, g32p_row02_traceSegment_059_1269_0013, g32p_row02_traceSegment_059_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1242 54 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1242 27 27, g32p_row02_traceSegment_059_1242_0027, g32p_row02_traceSegment_059_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 1188 108 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1188 54 54, g32p_row02_traceSegment_059_1188_0054, g32p_row02_traceSegment_059_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 1080 216 = [4, 0, 0, 0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1080 108 108, g32p_row02_traceSegment_059_1080_0108, g32p_row02_traceSegment_059_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_059 864 432 = [5, 0, 0, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 864 216 216, g32p_row02_traceSegment_059_0864_0216, g32p_row02_traceSegment_059_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1296 13 14, g32p_row02_traceSegment_059_1296_0013, g32p_row02_traceSegment_059_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1323 13 14, g32p_row02_traceSegment_059_1323_0013, g32p_row02_traceSegment_059_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1296 27 27, g32p_row02_traceSegment_059_1296_0027, g32p_row02_traceSegment_059_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1350 13 14, g32p_row02_traceSegment_059_1350_0013, g32p_row02_traceSegment_059_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1390 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1377 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1377 13 14, g32p_row02_traceSegment_059_1377_0013, g32p_row02_traceSegment_059_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1350 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1350 27 27, g32p_row02_traceSegment_059_1350_0027, g32p_row02_traceSegment_059_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 1296 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1296 54 54, g32p_row02_traceSegment_059_1296_0054, g32p_row02_traceSegment_059_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1404 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1404 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1404 13 14, g32p_row02_traceSegment_059_1404_0013, g32p_row02_traceSegment_059_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1431 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1444 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1431 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1431 13 14, g32p_row02_traceSegment_059_1431_0013, g32p_row02_traceSegment_059_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1404 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1404 27 27, g32p_row02_traceSegment_059_1404_0027, g32p_row02_traceSegment_059_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1458 13 14, g32p_row02_traceSegment_059_1458_0013, g32p_row02_traceSegment_059_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1498 14 = [2, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1485 27 = [2, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1485 13 14, g32p_row02_traceSegment_059_1485_0013, g32p_row02_traceSegment_059_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1458 54 = [2, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1458 27 27, g32p_row02_traceSegment_059_1458_0027, g32p_row02_traceSegment_059_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 1404 108 = [2, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1404 54 54, g32p_row02_traceSegment_059_1404_0054, g32p_row02_traceSegment_059_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 1296 216 = [2, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1296 108 108, g32p_row02_traceSegment_059_1296_0108, g32p_row02_traceSegment_059_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1512 13 14, g32p_row02_traceSegment_059_1512_0013, g32p_row02_traceSegment_059_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1539 13 = [2, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1539 27 = [2, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1539 13 14, g32p_row02_traceSegment_059_1539_0013, g32p_row02_traceSegment_059_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1512 54 = [2, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1512 27 27, g32p_row02_traceSegment_059_1512_0027, g32p_row02_traceSegment_059_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1579 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1566 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1566 13 14, g32p_row02_traceSegment_059_1566_0013, g32p_row02_traceSegment_059_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1593 13 14, g32p_row02_traceSegment_059_1593_0013, g32p_row02_traceSegment_059_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1566 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1566 27 27, g32p_row02_traceSegment_059_1566_0027, g32p_row02_traceSegment_059_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 1512 108 = [2, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1512 54 54, g32p_row02_traceSegment_059_1512_0054, g32p_row02_traceSegment_059_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1620 13 14, g32p_row02_traceSegment_059_1620_0013, g32p_row02_traceSegment_059_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1660 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1647 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1647 13 14, g32p_row02_traceSegment_059_1647_0013, g32p_row02_traceSegment_059_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1620 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1620 27 27, g32p_row02_traceSegment_059_1620_0027, g32p_row02_traceSegment_059_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1674 13 14, g32p_row02_traceSegment_059_1674_0013, g32p_row02_traceSegment_059_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1701 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1714 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1701 27 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1701 13 14, g32p_row02_traceSegment_059_1701_0013, g32p_row02_traceSegment_059_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1674 54 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1674 27 27, g32p_row02_traceSegment_059_1674_0027, g32p_row02_traceSegment_059_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 1620 108 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1620 54 54, g32p_row02_traceSegment_059_1620_0054, g32p_row02_traceSegment_059_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 1512 216 = [2, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1512 108 108, g32p_row02_traceSegment_059_1512_0108, g32p_row02_traceSegment_059_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_059 1296 432 = [4, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1296 216 216, g32p_row02_traceSegment_059_1296_0216, g32p_row02_traceSegment_059_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_059 864 864 = [9, 0, 0, 0, 0, 46] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 864 432 432, g32p_row02_traceSegment_059_0864_0432, g32p_row02_traceSegment_059_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_059 0 1728 = [21, 0, 0, 0, 0, 56] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 0 864 864, g32p_row02_traceSegment_059_0000_0864, g32p_row02_traceSegment_059_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1728 13 14, g32p_row02_traceSegment_059_1728_0013, g32p_row02_traceSegment_059_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1755 13 14, g32p_row02_traceSegment_059_1755_0013, g32p_row02_traceSegment_059_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1728 27 27, g32p_row02_traceSegment_059_1728_0027, g32p_row02_traceSegment_059_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1782 13 14, g32p_row02_traceSegment_059_1782_0013, g32p_row02_traceSegment_059_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1822 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1809 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1809 13 14, g32p_row02_traceSegment_059_1809_0013, g32p_row02_traceSegment_059_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1782 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1782 27 27, g32p_row02_traceSegment_059_1782_0027, g32p_row02_traceSegment_059_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 1728 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1728 54 54, g32p_row02_traceSegment_059_1728_0054, g32p_row02_traceSegment_059_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1836 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1836 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1836 13 14, g32p_row02_traceSegment_059_1836_0013, g32p_row02_traceSegment_059_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1863 13 14, g32p_row02_traceSegment_059_1863_0013, g32p_row02_traceSegment_059_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1836 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1836 27 27, g32p_row02_traceSegment_059_1836_0027, g32p_row02_traceSegment_059_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1890 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1903 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1890 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1890 13 14, g32p_row02_traceSegment_059_1890_0013, g32p_row02_traceSegment_059_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1917 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1930 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1917 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1917 13 14, g32p_row02_traceSegment_059_1917_0013, g32p_row02_traceSegment_059_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1890 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1890 27 27, g32p_row02_traceSegment_059_1890_0027, g32p_row02_traceSegment_059_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 1836 108 = [4, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1836 54 54, g32p_row02_traceSegment_059_1836_0054, g32p_row02_traceSegment_059_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 1728 216 = [4, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1728 108 108, g32p_row02_traceSegment_059_1728_0108, g32p_row02_traceSegment_059_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1944 13 14, g32p_row02_traceSegment_059_1944_0013, g32p_row02_traceSegment_059_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1971 13 14, g32p_row02_traceSegment_059_1971_0013, g32p_row02_traceSegment_059_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1944 27 27, g32p_row02_traceSegment_059_1944_0027, g32p_row02_traceSegment_059_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1998 13 14, g32p_row02_traceSegment_059_1998_0013, g32p_row02_traceSegment_059_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2025 13 14, g32p_row02_traceSegment_059_2025_0013, g32p_row02_traceSegment_059_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1998 27 27, g32p_row02_traceSegment_059_1998_0027, g32p_row02_traceSegment_059_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1944 54 54, g32p_row02_traceSegment_059_1944_0054, g32p_row02_traceSegment_059_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2052 13 14, g32p_row02_traceSegment_059_2052_0013, g32p_row02_traceSegment_059_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2079 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2079 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2079 13 14, g32p_row02_traceSegment_059_2079_0013, g32p_row02_traceSegment_059_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2052 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2052 27 27, g32p_row02_traceSegment_059_2052_0027, g32p_row02_traceSegment_059_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2106 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2119 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2106 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2106 13 14, g32p_row02_traceSegment_059_2106_0013, g32p_row02_traceSegment_059_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2133 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2133 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2133 13 14, g32p_row02_traceSegment_059_2133_0013, g32p_row02_traceSegment_059_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2106 54 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2106 27 27, g32p_row02_traceSegment_059_2106_0027, g32p_row02_traceSegment_059_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 2052 108 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2052 54 54, g32p_row02_traceSegment_059_2052_0054, g32p_row02_traceSegment_059_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 1944 216 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1944 108 108, g32p_row02_traceSegment_059_1944_0108, g32p_row02_traceSegment_059_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_059 1728 432 = [4, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1728 216 216, g32p_row02_traceSegment_059_1728_0216, g32p_row02_traceSegment_059_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2160 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2160 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2160 13 14, g32p_row02_traceSegment_059_2160_0013, g32p_row02_traceSegment_059_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2187 13 14, g32p_row02_traceSegment_059_2187_0013, g32p_row02_traceSegment_059_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2160 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2160 27 27, g32p_row02_traceSegment_059_2160_0027, g32p_row02_traceSegment_059_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2214 13 14, g32p_row02_traceSegment_059_2214_0013, g32p_row02_traceSegment_059_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2241 13 14, g32p_row02_traceSegment_059_2241_0013, g32p_row02_traceSegment_059_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2214 27 27, g32p_row02_traceSegment_059_2214_0027, g32p_row02_traceSegment_059_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 2160 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2160 54 54, g32p_row02_traceSegment_059_2160_0054, g32p_row02_traceSegment_059_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2268 13 14, g32p_row02_traceSegment_059_2268_0013, g32p_row02_traceSegment_059_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2295 13 14, g32p_row02_traceSegment_059_2295_0013, g32p_row02_traceSegment_059_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2268 27 27, g32p_row02_traceSegment_059_2268_0027, g32p_row02_traceSegment_059_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2322 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2335 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2322 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2322 13 14, g32p_row02_traceSegment_059_2322_0013, g32p_row02_traceSegment_059_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2349 13 14, g32p_row02_traceSegment_059_2349_0013, g32p_row02_traceSegment_059_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2322 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2322 27 27, g32p_row02_traceSegment_059_2322_0027, g32p_row02_traceSegment_059_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 2268 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2268 54 54, g32p_row02_traceSegment_059_2268_0054, g32p_row02_traceSegment_059_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 2160 216 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2160 108 108, g32p_row02_traceSegment_059_2160_0108, g32p_row02_traceSegment_059_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2376 13 = [0, 0, 0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2389 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2376 27 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2376 13 14, g32p_row02_traceSegment_059_2376_0013, g32p_row02_traceSegment_059_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2403 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2416 14 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2403 27 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2403 13 14, g32p_row02_traceSegment_059_2403_0013, g32p_row02_traceSegment_059_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2376 54 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2376 27 27, g32p_row02_traceSegment_059_2376_0027, g32p_row02_traceSegment_059_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2430 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2430 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2430 13 14, g32p_row02_traceSegment_059_2430_0013, g32p_row02_traceSegment_059_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2457 13 14, g32p_row02_traceSegment_059_2457_0013, g32p_row02_traceSegment_059_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2430 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2430 27 27, g32p_row02_traceSegment_059_2430_0027, g32p_row02_traceSegment_059_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 2376 108 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2376 54 54, g32p_row02_traceSegment_059_2376_0054, g32p_row02_traceSegment_059_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2484 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2484 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2484 13 14, g32p_row02_traceSegment_059_2484_0013, g32p_row02_traceSegment_059_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2524 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2511 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2511 13 14, g32p_row02_traceSegment_059_2511_0013, g32p_row02_traceSegment_059_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2484 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2484 27 27, g32p_row02_traceSegment_059_2484_0027, g32p_row02_traceSegment_059_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2538 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2538 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2538 13 14, g32p_row02_traceSegment_059_2538_0013, g32p_row02_traceSegment_059_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2565 13 14, g32p_row02_traceSegment_059_2565_0013, g32p_row02_traceSegment_059_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2538 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2538 27 27, g32p_row02_traceSegment_059_2538_0027, g32p_row02_traceSegment_059_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 2484 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2484 54 54, g32p_row02_traceSegment_059_2484_0054, g32p_row02_traceSegment_059_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 2376 216 = [3, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2376 108 108, g32p_row02_traceSegment_059_2376_0108, g32p_row02_traceSegment_059_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_059 2160 432 = [3, 0, 0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2160 216 216, g32p_row02_traceSegment_059_2160_0216, g32p_row02_traceSegment_059_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_059 1728 864 = [7, 0, 0, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1728 432 432, g32p_row02_traceSegment_059_1728_0432, g32p_row02_traceSegment_059_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2592 13 14, g32p_row02_traceSegment_059_2592_0013, g32p_row02_traceSegment_059_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2619 13 14, g32p_row02_traceSegment_059_2619_0013, g32p_row02_traceSegment_059_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2592 27 27, g32p_row02_traceSegment_059_2592_0027, g32p_row02_traceSegment_059_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2646 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2646 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2646 13 14, g32p_row02_traceSegment_059_2646_0013, g32p_row02_traceSegment_059_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2673 13 14, g32p_row02_traceSegment_059_2673_0013, g32p_row02_traceSegment_059_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2646 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2646 27 27, g32p_row02_traceSegment_059_2646_0027, g32p_row02_traceSegment_059_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 2592 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2592 54 54, g32p_row02_traceSegment_059_2592_0054, g32p_row02_traceSegment_059_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2700 13 14, g32p_row02_traceSegment_059_2700_0013, g32p_row02_traceSegment_059_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2727 13 14, g32p_row02_traceSegment_059_2727_0013, g32p_row02_traceSegment_059_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2700 27 27, g32p_row02_traceSegment_059_2700_0027, g32p_row02_traceSegment_059_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2754 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2767 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2754 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2754 13 14, g32p_row02_traceSegment_059_2754_0013, g32p_row02_traceSegment_059_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2781 13 14, g32p_row02_traceSegment_059_2781_0013, g32p_row02_traceSegment_059_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2754 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2754 27 27, g32p_row02_traceSegment_059_2754_0027, g32p_row02_traceSegment_059_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 2700 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2700 54 54, g32p_row02_traceSegment_059_2700_0054, g32p_row02_traceSegment_059_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 2592 216 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2592 108 108, g32p_row02_traceSegment_059_2592_0108, g32p_row02_traceSegment_059_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2808 13 14, g32p_row02_traceSegment_059_2808_0013, g32p_row02_traceSegment_059_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2835 13 14, g32p_row02_traceSegment_059_2835_0013, g32p_row02_traceSegment_059_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2808 27 27, g32p_row02_traceSegment_059_2808_0027, g32p_row02_traceSegment_059_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2862 13 14, g32p_row02_traceSegment_059_2862_0013, g32p_row02_traceSegment_059_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2889 13 14, g32p_row02_traceSegment_059_2889_0013, g32p_row02_traceSegment_059_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2862 27 27, g32p_row02_traceSegment_059_2862_0027, g32p_row02_traceSegment_059_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2808 54 54, g32p_row02_traceSegment_059_2808_0054, g32p_row02_traceSegment_059_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2916 13 14, g32p_row02_traceSegment_059_2916_0013, g32p_row02_traceSegment_059_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2943 13 14, g32p_row02_traceSegment_059_2943_0013, g32p_row02_traceSegment_059_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2916 27 27, g32p_row02_traceSegment_059_2916_0027, g32p_row02_traceSegment_059_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2970 13 14, g32p_row02_traceSegment_059_2970_0013, g32p_row02_traceSegment_059_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 2997 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 2997 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2997 13 14, g32p_row02_traceSegment_059_2997_0013, g32p_row02_traceSegment_059_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 2970 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2970 27 27, g32p_row02_traceSegment_059_2970_0027, g32p_row02_traceSegment_059_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 2916 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2916 54 54, g32p_row02_traceSegment_059_2916_0054, g32p_row02_traceSegment_059_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 2808 216 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2808 108 108, g32p_row02_traceSegment_059_2808_0108, g32p_row02_traceSegment_059_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_059 2592 432 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2592 216 216, g32p_row02_traceSegment_059_2592_0216, g32p_row02_traceSegment_059_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3024 13 14, g32p_row02_traceSegment_059_3024_0013, g32p_row02_traceSegment_059_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3051 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3064 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3051 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3051 13 14, g32p_row02_traceSegment_059_3051_0013, g32p_row02_traceSegment_059_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 3024 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3024 27 27, g32p_row02_traceSegment_059_3024_0027, g32p_row02_traceSegment_059_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3078 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3078 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3078 13 14, g32p_row02_traceSegment_059_3078_0013, g32p_row02_traceSegment_059_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3118 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3105 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3105 13 14, g32p_row02_traceSegment_059_3105_0013, g32p_row02_traceSegment_059_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 3078 54 = [2, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3078 27 27, g32p_row02_traceSegment_059_3078_0027, g32p_row02_traceSegment_059_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 3024 108 = [4, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3024 54 54, g32p_row02_traceSegment_059_3024_0054, g32p_row02_traceSegment_059_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3132 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3132 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3132 13 14, g32p_row02_traceSegment_059_3132_0013, g32p_row02_traceSegment_059_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3159 13 14, g32p_row02_traceSegment_059_3159_0013, g32p_row02_traceSegment_059_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 3132 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3132 27 27, g32p_row02_traceSegment_059_3132_0027, g32p_row02_traceSegment_059_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3186 13 14, g32p_row02_traceSegment_059_3186_0013, g32p_row02_traceSegment_059_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3213 13 14, g32p_row02_traceSegment_059_3213_0013, g32p_row02_traceSegment_059_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3186 27 27, g32p_row02_traceSegment_059_3186_0027, g32p_row02_traceSegment_059_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 3132 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3132 54 54, g32p_row02_traceSegment_059_3132_0054, g32p_row02_traceSegment_059_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 3024 216 = [4, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3024 108 108, g32p_row02_traceSegment_059_3024_0108, g32p_row02_traceSegment_059_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3240 13 14, g32p_row02_traceSegment_059_3240_0013, g32p_row02_traceSegment_059_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3267 13 14, g32p_row02_traceSegment_059_3267_0013, g32p_row02_traceSegment_059_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3240 27 27, g32p_row02_traceSegment_059_3240_0027, g32p_row02_traceSegment_059_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3294 13 14, g32p_row02_traceSegment_059_3294_0013, g32p_row02_traceSegment_059_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3321 13 14, g32p_row02_traceSegment_059_3321_0013, g32p_row02_traceSegment_059_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3294 27 27, g32p_row02_traceSegment_059_3294_0027, g32p_row02_traceSegment_059_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3240 54 54, g32p_row02_traceSegment_059_3240_0054, g32p_row02_traceSegment_059_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3348 13 14, g32p_row02_traceSegment_059_3348_0013, g32p_row02_traceSegment_059_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3375 13 14, g32p_row02_traceSegment_059_3375_0013, g32p_row02_traceSegment_059_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3348 27 27, g32p_row02_traceSegment_059_3348_0027, g32p_row02_traceSegment_059_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3402 13 14, g32p_row02_traceSegment_059_3402_0013, g32p_row02_traceSegment_059_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_059 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_059 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_059_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_059 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3429 13 14, g32p_row02_traceSegment_059_3429_0013, g32p_row02_traceSegment_059_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_059 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3402 27 27, g32p_row02_traceSegment_059_3402_0027, g32p_row02_traceSegment_059_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_059 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3348 54 54, g32p_row02_traceSegment_059_3348_0054, g32p_row02_traceSegment_059_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_059 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3240 108 108, g32p_row02_traceSegment_059_3240_0108, g32p_row02_traceSegment_059_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_059_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_059 3024 432 = [4, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 3024 216 216, g32p_row02_traceSegment_059_3024_0216, g32p_row02_traceSegment_059_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_059_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_059 2592 864 = [4, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 2592 432 432, g32p_row02_traceSegment_059_2592_0432, g32p_row02_traceSegment_059_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_059_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_059 1728 1728 = [11, 0, 0, 0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 1728 864 864, g32p_row02_traceSegment_059_1728_0864, g32p_row02_traceSegment_059_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_059_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_059 0 3456 = [32, 0, 0, 0, 0, 96] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_059 0 1728 1728, g32p_row02_traceSegment_059_0000_1728, g32p_row02_traceSegment_059_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 59 = [32, 0, 0, 0, 0, 96] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_059_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_061 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 61 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_061_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 0 13 14, g32p_row02_traceSegment_061_0000_0013, g32p_row02_traceSegment_061_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 27 13 14, g32p_row02_traceSegment_061_0027_0013, g32p_row02_traceSegment_061_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 0 27 27, g32p_row02_traceSegment_061_0000_0027, g32p_row02_traceSegment_061_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 54 13 14, g32p_row02_traceSegment_061_0054_0013, g32p_row02_traceSegment_061_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 81 13 14, g32p_row02_traceSegment_061_0081_0013, g32p_row02_traceSegment_061_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 54 27 27, g32p_row02_traceSegment_061_0054_0027, g32p_row02_traceSegment_061_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 0 54 54, g32p_row02_traceSegment_061_0000_0054, g32p_row02_traceSegment_061_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 108 13 14, g32p_row02_traceSegment_061_0108_0013, g32p_row02_traceSegment_061_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 135 13 14, g32p_row02_traceSegment_061_0135_0013, g32p_row02_traceSegment_061_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 108 27 27, g32p_row02_traceSegment_061_0108_0027, g32p_row02_traceSegment_061_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 162 13 14, g32p_row02_traceSegment_061_0162_0013, g32p_row02_traceSegment_061_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 189 13 14, g32p_row02_traceSegment_061_0189_0013, g32p_row02_traceSegment_061_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 162 27 27, g32p_row02_traceSegment_061_0162_0027, g32p_row02_traceSegment_061_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 108 54 54, g32p_row02_traceSegment_061_0108_0054, g32p_row02_traceSegment_061_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 0 108 108, g32p_row02_traceSegment_061_0000_0108, g32p_row02_traceSegment_061_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 216 13 14, g32p_row02_traceSegment_061_0216_0013, g32p_row02_traceSegment_061_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 243 13 14, g32p_row02_traceSegment_061_0243_0013, g32p_row02_traceSegment_061_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 216 27 27, g32p_row02_traceSegment_061_0216_0027, g32p_row02_traceSegment_061_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 270 13 14, g32p_row02_traceSegment_061_0270_0013, g32p_row02_traceSegment_061_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 297 13 14, g32p_row02_traceSegment_061_0297_0013, g32p_row02_traceSegment_061_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 270 27 27, g32p_row02_traceSegment_061_0270_0027, g32p_row02_traceSegment_061_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 216 54 54, g32p_row02_traceSegment_061_0216_0054, g32p_row02_traceSegment_061_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 324 13 14, g32p_row02_traceSegment_061_0324_0013, g32p_row02_traceSegment_061_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 351 13 14, g32p_row02_traceSegment_061_0351_0013, g32p_row02_traceSegment_061_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 324 27 27, g32p_row02_traceSegment_061_0324_0027, g32p_row02_traceSegment_061_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 378 13 14, g32p_row02_traceSegment_061_0378_0013, g32p_row02_traceSegment_061_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 405 13 14, g32p_row02_traceSegment_061_0405_0013, g32p_row02_traceSegment_061_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 378 27 27, g32p_row02_traceSegment_061_0378_0027, g32p_row02_traceSegment_061_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 324 54 54, g32p_row02_traceSegment_061_0324_0054, g32p_row02_traceSegment_061_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 216 108 108, g32p_row02_traceSegment_061_0216_0108, g32p_row02_traceSegment_061_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_061 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 0 216 216, g32p_row02_traceSegment_061_0000_0216, g32p_row02_traceSegment_061_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 432 13 14, g32p_row02_traceSegment_061_0432_0013, g32p_row02_traceSegment_061_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 472 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 459 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 459 13 14, g32p_row02_traceSegment_061_0459_0013, g32p_row02_traceSegment_061_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 432 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 432 27 27, g32p_row02_traceSegment_061_0432_0027, g32p_row02_traceSegment_061_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 486 13 14, g32p_row02_traceSegment_061_0486_0013, g32p_row02_traceSegment_061_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 513 13 14, g32p_row02_traceSegment_061_0513_0013, g32p_row02_traceSegment_061_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 486 27 27, g32p_row02_traceSegment_061_0486_0027, g32p_row02_traceSegment_061_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 432 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 432 54 54, g32p_row02_traceSegment_061_0432_0054, g32p_row02_traceSegment_061_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 540 13 14, g32p_row02_traceSegment_061_0540_0013, g32p_row02_traceSegment_061_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 580 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 567 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 567 13 14, g32p_row02_traceSegment_061_0567_0013, g32p_row02_traceSegment_061_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 540 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 540 27 27, g32p_row02_traceSegment_061_0540_0027, g32p_row02_traceSegment_061_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 594 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 607 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 594 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 594 13 14, g32p_row02_traceSegment_061_0594_0013, g32p_row02_traceSegment_061_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 621 13 14, g32p_row02_traceSegment_061_0621_0013, g32p_row02_traceSegment_061_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 594 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 594 27 27, g32p_row02_traceSegment_061_0594_0027, g32p_row02_traceSegment_061_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 540 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 540 54 54, g32p_row02_traceSegment_061_0540_0054, g32p_row02_traceSegment_061_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 432 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 432 108 108, g32p_row02_traceSegment_061_0432_0108, g32p_row02_traceSegment_061_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 648 13 14, g32p_row02_traceSegment_061_0648_0013, g32p_row02_traceSegment_061_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 675 13 14, g32p_row02_traceSegment_061_0675_0013, g32p_row02_traceSegment_061_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 648 27 27, g32p_row02_traceSegment_061_0648_0027, g32p_row02_traceSegment_061_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 702 13 14, g32p_row02_traceSegment_061_0702_0013, g32p_row02_traceSegment_061_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 729 13 14, g32p_row02_traceSegment_061_0729_0013, g32p_row02_traceSegment_061_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 702 27 27, g32p_row02_traceSegment_061_0702_0027, g32p_row02_traceSegment_061_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 648 54 54, g32p_row02_traceSegment_061_0648_0054, g32p_row02_traceSegment_061_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 756 13 14, g32p_row02_traceSegment_061_0756_0013, g32p_row02_traceSegment_061_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 783 13 14, g32p_row02_traceSegment_061_0783_0013, g32p_row02_traceSegment_061_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 756 27 27, g32p_row02_traceSegment_061_0756_0027, g32p_row02_traceSegment_061_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 810 13 14, g32p_row02_traceSegment_061_0810_0013, g32p_row02_traceSegment_061_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 837 13 14, g32p_row02_traceSegment_061_0837_0013, g32p_row02_traceSegment_061_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 810 27 27, g32p_row02_traceSegment_061_0810_0027, g32p_row02_traceSegment_061_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 756 54 54, g32p_row02_traceSegment_061_0756_0054, g32p_row02_traceSegment_061_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 648 108 108, g32p_row02_traceSegment_061_0648_0108, g32p_row02_traceSegment_061_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_061 432 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 432 216 216, g32p_row02_traceSegment_061_0432_0216, g32p_row02_traceSegment_061_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_061 0 864 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 0 432 432, g32p_row02_traceSegment_061_0000_0432, g32p_row02_traceSegment_061_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 864 13 14, g32p_row02_traceSegment_061_0864_0013, g32p_row02_traceSegment_061_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 891 13 14, g32p_row02_traceSegment_061_0891_0013, g32p_row02_traceSegment_061_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 864 27 27, g32p_row02_traceSegment_061_0864_0027, g32p_row02_traceSegment_061_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 931 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 918 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 918 13 14, g32p_row02_traceSegment_061_0918_0013, g32p_row02_traceSegment_061_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 945 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 958 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 945 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 945 13 14, g32p_row02_traceSegment_061_0945_0013, g32p_row02_traceSegment_061_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 918 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 918 27 27, g32p_row02_traceSegment_061_0918_0027, g32p_row02_traceSegment_061_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 864 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 864 54 54, g32p_row02_traceSegment_061_0864_0054, g32p_row02_traceSegment_061_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 972 13 14, g32p_row02_traceSegment_061_0972_0013, g32p_row02_traceSegment_061_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 999 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 999 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 999 13 14, g32p_row02_traceSegment_061_0999_0013, g32p_row02_traceSegment_061_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 972 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 972 27 27, g32p_row02_traceSegment_061_0972_0027, g32p_row02_traceSegment_061_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1026 13 14, g32p_row02_traceSegment_061_1026_0013, g32p_row02_traceSegment_061_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1053 13 14, g32p_row02_traceSegment_061_1053_0013, g32p_row02_traceSegment_061_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1026 27 27, g32p_row02_traceSegment_061_1026_0027, g32p_row02_traceSegment_061_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 972 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 972 54 54, g32p_row02_traceSegment_061_0972_0054, g32p_row02_traceSegment_061_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 864 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 864 108 108, g32p_row02_traceSegment_061_0864_0108, g32p_row02_traceSegment_061_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1080 13 14, g32p_row02_traceSegment_061_1080_0013, g32p_row02_traceSegment_061_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1107 13 14, g32p_row02_traceSegment_061_1107_0013, g32p_row02_traceSegment_061_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1080 27 27, g32p_row02_traceSegment_061_1080_0027, g32p_row02_traceSegment_061_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1134 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1134 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1134 13 14, g32p_row02_traceSegment_061_1134_0013, g32p_row02_traceSegment_061_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1161 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1161 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1161 13 14, g32p_row02_traceSegment_061_1161_0013, g32p_row02_traceSegment_061_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1134 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1134 27 27, g32p_row02_traceSegment_061_1134_0027, g32p_row02_traceSegment_061_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 1080 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1080 54 54, g32p_row02_traceSegment_061_1080_0054, g32p_row02_traceSegment_061_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1188 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1201 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1188 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1188 13 14, g32p_row02_traceSegment_061_1188_0013, g32p_row02_traceSegment_061_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1215 13 14, g32p_row02_traceSegment_061_1215_0013, g32p_row02_traceSegment_061_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1188 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1188 27 27, g32p_row02_traceSegment_061_1188_0027, g32p_row02_traceSegment_061_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1255 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1242 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1242 13 14, g32p_row02_traceSegment_061_1242_0013, g32p_row02_traceSegment_061_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1282 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1269 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1269 13 14, g32p_row02_traceSegment_061_1269_0013, g32p_row02_traceSegment_061_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1242 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1242 27 27, g32p_row02_traceSegment_061_1242_0027, g32p_row02_traceSegment_061_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 1188 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1188 54 54, g32p_row02_traceSegment_061_1188_0054, g32p_row02_traceSegment_061_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 1080 216 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1080 108 108, g32p_row02_traceSegment_061_1080_0108, g32p_row02_traceSegment_061_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_061 864 432 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 864 216 216, g32p_row02_traceSegment_061_0864_0216, g32p_row02_traceSegment_061_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1296 13 14, g32p_row02_traceSegment_061_1296_0013, g32p_row02_traceSegment_061_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1323 13 14, g32p_row02_traceSegment_061_1323_0013, g32p_row02_traceSegment_061_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1296 27 27, g32p_row02_traceSegment_061_1296_0027, g32p_row02_traceSegment_061_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1350 13 14, g32p_row02_traceSegment_061_1350_0013, g32p_row02_traceSegment_061_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1377 13 14, g32p_row02_traceSegment_061_1377_0013, g32p_row02_traceSegment_061_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1350 27 27, g32p_row02_traceSegment_061_1350_0027, g32p_row02_traceSegment_061_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1296 54 54, g32p_row02_traceSegment_061_1296_0054, g32p_row02_traceSegment_061_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1404 13 14, g32p_row02_traceSegment_061_1404_0013, g32p_row02_traceSegment_061_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1431 13 14, g32p_row02_traceSegment_061_1431_0013, g32p_row02_traceSegment_061_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1404 27 27, g32p_row02_traceSegment_061_1404_0027, g32p_row02_traceSegment_061_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1458 13 14, g32p_row02_traceSegment_061_1458_0013, g32p_row02_traceSegment_061_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1485 13 14, g32p_row02_traceSegment_061_1485_0013, g32p_row02_traceSegment_061_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1458 27 27, g32p_row02_traceSegment_061_1458_0027, g32p_row02_traceSegment_061_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1404 54 54, g32p_row02_traceSegment_061_1404_0054, g32p_row02_traceSegment_061_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1296 108 108, g32p_row02_traceSegment_061_1296_0108, g32p_row02_traceSegment_061_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1512 13 14, g32p_row02_traceSegment_061_1512_0013, g32p_row02_traceSegment_061_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1552 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1539 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1539 13 14, g32p_row02_traceSegment_061_1539_0013, g32p_row02_traceSegment_061_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1512 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1512 27 27, g32p_row02_traceSegment_061_1512_0027, g32p_row02_traceSegment_061_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1566 13 14, g32p_row02_traceSegment_061_1566_0013, g32p_row02_traceSegment_061_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1593 13 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1606 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1593 27 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1593 13 14, g32p_row02_traceSegment_061_1593_0013, g32p_row02_traceSegment_061_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1566 54 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1566 27 27, g32p_row02_traceSegment_061_1566_0027, g32p_row02_traceSegment_061_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 1512 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1512 54 54, g32p_row02_traceSegment_061_1512_0054, g32p_row02_traceSegment_061_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1620 13 14, g32p_row02_traceSegment_061_1620_0013, g32p_row02_traceSegment_061_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1647 13 14, g32p_row02_traceSegment_061_1647_0013, g32p_row02_traceSegment_061_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1620 27 27, g32p_row02_traceSegment_061_1620_0027, g32p_row02_traceSegment_061_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1687 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1674 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1674 13 14, g32p_row02_traceSegment_061_1674_0013, g32p_row02_traceSegment_061_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1701 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1701 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1701 13 14, g32p_row02_traceSegment_061_1701_0013, g32p_row02_traceSegment_061_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1674 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1674 27 27, g32p_row02_traceSegment_061_1674_0027, g32p_row02_traceSegment_061_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 1620 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1620 54 54, g32p_row02_traceSegment_061_1620_0054, g32p_row02_traceSegment_061_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 1512 216 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1512 108 108, g32p_row02_traceSegment_061_1512_0108, g32p_row02_traceSegment_061_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_061 1296 432 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1296 216 216, g32p_row02_traceSegment_061_1296_0216, g32p_row02_traceSegment_061_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_061 864 864 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 864 432 432, g32p_row02_traceSegment_061_0864_0432, g32p_row02_traceSegment_061_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_061 0 1728 = [0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 0 864 864, g32p_row02_traceSegment_061_0000_0864, g32p_row02_traceSegment_061_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1728 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1728 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1728 13 14, g32p_row02_traceSegment_061_1728_0013, g32p_row02_traceSegment_061_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1755 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1755 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1755 13 14, g32p_row02_traceSegment_061_1755_0013, g32p_row02_traceSegment_061_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1728 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1728 27 27, g32p_row02_traceSegment_061_1728_0027, g32p_row02_traceSegment_061_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1782 13 14, g32p_row02_traceSegment_061_1782_0013, g32p_row02_traceSegment_061_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1809 13 14, g32p_row02_traceSegment_061_1809_0013, g32p_row02_traceSegment_061_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1782 27 27, g32p_row02_traceSegment_061_1782_0027, g32p_row02_traceSegment_061_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 1728 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1728 54 54, g32p_row02_traceSegment_061_1728_0054, g32p_row02_traceSegment_061_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1836 13 14, g32p_row02_traceSegment_061_1836_0013, g32p_row02_traceSegment_061_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1863 13 14, g32p_row02_traceSegment_061_1863_0013, g32p_row02_traceSegment_061_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1836 27 27, g32p_row02_traceSegment_061_1836_0027, g32p_row02_traceSegment_061_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1890 13 14, g32p_row02_traceSegment_061_1890_0013, g32p_row02_traceSegment_061_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1917 13 14, g32p_row02_traceSegment_061_1917_0013, g32p_row02_traceSegment_061_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1890 27 27, g32p_row02_traceSegment_061_1890_0027, g32p_row02_traceSegment_061_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1836 54 54, g32p_row02_traceSegment_061_1836_0054, g32p_row02_traceSegment_061_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 1728 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1728 108 108, g32p_row02_traceSegment_061_1728_0108, g32p_row02_traceSegment_061_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1944 13 14, g32p_row02_traceSegment_061_1944_0013, g32p_row02_traceSegment_061_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1971 13 14, g32p_row02_traceSegment_061_1971_0013, g32p_row02_traceSegment_061_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1944 27 27, g32p_row02_traceSegment_061_1944_0027, g32p_row02_traceSegment_061_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1998 13 14, g32p_row02_traceSegment_061_1998_0013, g32p_row02_traceSegment_061_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2025 13 14, g32p_row02_traceSegment_061_2025_0013, g32p_row02_traceSegment_061_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1998 27 27, g32p_row02_traceSegment_061_1998_0027, g32p_row02_traceSegment_061_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1944 54 54, g32p_row02_traceSegment_061_1944_0054, g32p_row02_traceSegment_061_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2052 13 14, g32p_row02_traceSegment_061_2052_0013, g32p_row02_traceSegment_061_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2079 13 14, g32p_row02_traceSegment_061_2079_0013, g32p_row02_traceSegment_061_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2052 27 27, g32p_row02_traceSegment_061_2052_0027, g32p_row02_traceSegment_061_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2106 13 14, g32p_row02_traceSegment_061_2106_0013, g32p_row02_traceSegment_061_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2133 13 14, g32p_row02_traceSegment_061_2133_0013, g32p_row02_traceSegment_061_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2106 27 27, g32p_row02_traceSegment_061_2106_0027, g32p_row02_traceSegment_061_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2052 54 54, g32p_row02_traceSegment_061_2052_0054, g32p_row02_traceSegment_061_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1944 108 108, g32p_row02_traceSegment_061_1944_0108, g32p_row02_traceSegment_061_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_061 1728 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1728 216 216, g32p_row02_traceSegment_061_1728_0216, g32p_row02_traceSegment_061_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2160 13 14, g32p_row02_traceSegment_061_2160_0013, g32p_row02_traceSegment_061_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2187 13 14, g32p_row02_traceSegment_061_2187_0013, g32p_row02_traceSegment_061_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2160 27 27, g32p_row02_traceSegment_061_2160_0027, g32p_row02_traceSegment_061_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2214 13 14, g32p_row02_traceSegment_061_2214_0013, g32p_row02_traceSegment_061_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2241 13 14, g32p_row02_traceSegment_061_2241_0013, g32p_row02_traceSegment_061_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2214 27 27, g32p_row02_traceSegment_061_2214_0027, g32p_row02_traceSegment_061_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2160 54 54, g32p_row02_traceSegment_061_2160_0054, g32p_row02_traceSegment_061_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2268 13 14, g32p_row02_traceSegment_061_2268_0013, g32p_row02_traceSegment_061_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2295 13 14, g32p_row02_traceSegment_061_2295_0013, g32p_row02_traceSegment_061_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2268 27 27, g32p_row02_traceSegment_061_2268_0027, g32p_row02_traceSegment_061_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2322 13 14, g32p_row02_traceSegment_061_2322_0013, g32p_row02_traceSegment_061_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2349 13 14, g32p_row02_traceSegment_061_2349_0013, g32p_row02_traceSegment_061_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2322 27 27, g32p_row02_traceSegment_061_2322_0027, g32p_row02_traceSegment_061_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2268 54 54, g32p_row02_traceSegment_061_2268_0054, g32p_row02_traceSegment_061_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2160 108 108, g32p_row02_traceSegment_061_2160_0108, g32p_row02_traceSegment_061_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2376 13 14, g32p_row02_traceSegment_061_2376_0013, g32p_row02_traceSegment_061_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2403 13 14, g32p_row02_traceSegment_061_2403_0013, g32p_row02_traceSegment_061_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2376 27 27, g32p_row02_traceSegment_061_2376_0027, g32p_row02_traceSegment_061_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2443 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2430 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2430 13 14, g32p_row02_traceSegment_061_2430_0013, g32p_row02_traceSegment_061_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2457 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2470 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2457 27 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2457 13 14, g32p_row02_traceSegment_061_2457_0013, g32p_row02_traceSegment_061_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2430 54 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2430 27 27, g32p_row02_traceSegment_061_2430_0027, g32p_row02_traceSegment_061_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 2376 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2376 54 54, g32p_row02_traceSegment_061_2376_0054, g32p_row02_traceSegment_061_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2484 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2497 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2484 27 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2484 13 14, g32p_row02_traceSegment_061_2484_0013, g32p_row02_traceSegment_061_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2511 13 14, g32p_row02_traceSegment_061_2511_0013, g32p_row02_traceSegment_061_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2484 54 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2484 27 27, g32p_row02_traceSegment_061_2484_0027, g32p_row02_traceSegment_061_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2538 13 14, g32p_row02_traceSegment_061_2538_0013, g32p_row02_traceSegment_061_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2565 13 14, g32p_row02_traceSegment_061_2565_0013, g32p_row02_traceSegment_061_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2538 27 27, g32p_row02_traceSegment_061_2538_0027, g32p_row02_traceSegment_061_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 2484 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2484 54 54, g32p_row02_traceSegment_061_2484_0054, g32p_row02_traceSegment_061_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 2376 216 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2376 108 108, g32p_row02_traceSegment_061_2376_0108, g32p_row02_traceSegment_061_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_061 2160 432 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2160 216 216, g32p_row02_traceSegment_061_2160_0216, g32p_row02_traceSegment_061_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_061 1728 864 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1728 432 432, g32p_row02_traceSegment_061_1728_0432, g32p_row02_traceSegment_061_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2592 13 14, g32p_row02_traceSegment_061_2592_0013, g32p_row02_traceSegment_061_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2619 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2619 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2619 13 14, g32p_row02_traceSegment_061_2619_0013, g32p_row02_traceSegment_061_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2592 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2592 27 27, g32p_row02_traceSegment_061_2592_0027, g32p_row02_traceSegment_061_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2646 13 14, g32p_row02_traceSegment_061_2646_0013, g32p_row02_traceSegment_061_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2673 13 14, g32p_row02_traceSegment_061_2673_0013, g32p_row02_traceSegment_061_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2646 27 27, g32p_row02_traceSegment_061_2646_0027, g32p_row02_traceSegment_061_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 2592 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2592 54 54, g32p_row02_traceSegment_061_2592_0054, g32p_row02_traceSegment_061_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2700 13 14, g32p_row02_traceSegment_061_2700_0013, g32p_row02_traceSegment_061_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2727 13 14, g32p_row02_traceSegment_061_2727_0013, g32p_row02_traceSegment_061_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2700 27 27, g32p_row02_traceSegment_061_2700_0027, g32p_row02_traceSegment_061_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2754 13 14, g32p_row02_traceSegment_061_2754_0013, g32p_row02_traceSegment_061_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2781 13 14, g32p_row02_traceSegment_061_2781_0013, g32p_row02_traceSegment_061_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2754 27 27, g32p_row02_traceSegment_061_2754_0027, g32p_row02_traceSegment_061_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2700 54 54, g32p_row02_traceSegment_061_2700_0054, g32p_row02_traceSegment_061_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 2592 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2592 108 108, g32p_row02_traceSegment_061_2592_0108, g32p_row02_traceSegment_061_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2808 13 14, g32p_row02_traceSegment_061_2808_0013, g32p_row02_traceSegment_061_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2835 13 14, g32p_row02_traceSegment_061_2835_0013, g32p_row02_traceSegment_061_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2808 27 27, g32p_row02_traceSegment_061_2808_0027, g32p_row02_traceSegment_061_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2862 13 14, g32p_row02_traceSegment_061_2862_0013, g32p_row02_traceSegment_061_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2889 13 14, g32p_row02_traceSegment_061_2889_0013, g32p_row02_traceSegment_061_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2862 27 27, g32p_row02_traceSegment_061_2862_0027, g32p_row02_traceSegment_061_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2808 54 54, g32p_row02_traceSegment_061_2808_0054, g32p_row02_traceSegment_061_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2916 13 14, g32p_row02_traceSegment_061_2916_0013, g32p_row02_traceSegment_061_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2943 13 14, g32p_row02_traceSegment_061_2943_0013, g32p_row02_traceSegment_061_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2916 27 27, g32p_row02_traceSegment_061_2916_0027, g32p_row02_traceSegment_061_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2970 13 14, g32p_row02_traceSegment_061_2970_0013, g32p_row02_traceSegment_061_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 2997 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 2997 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2997 13 14, g32p_row02_traceSegment_061_2997_0013, g32p_row02_traceSegment_061_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 2970 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2970 27 27, g32p_row02_traceSegment_061_2970_0027, g32p_row02_traceSegment_061_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 2916 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2916 54 54, g32p_row02_traceSegment_061_2916_0054, g32p_row02_traceSegment_061_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 2808 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2808 108 108, g32p_row02_traceSegment_061_2808_0108, g32p_row02_traceSegment_061_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_061 2592 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2592 216 216, g32p_row02_traceSegment_061_2592_0216, g32p_row02_traceSegment_061_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3024 13 14, g32p_row02_traceSegment_061_3024_0013, g32p_row02_traceSegment_061_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3051 13 14, g32p_row02_traceSegment_061_3051_0013, g32p_row02_traceSegment_061_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3024 27 27, g32p_row02_traceSegment_061_3024_0027, g32p_row02_traceSegment_061_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3091 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3078 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3078 13 14, g32p_row02_traceSegment_061_3078_0013, g32p_row02_traceSegment_061_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3105 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3105 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3105 13 14, g32p_row02_traceSegment_061_3105_0013, g32p_row02_traceSegment_061_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 3078 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3078 27 27, g32p_row02_traceSegment_061_3078_0027, g32p_row02_traceSegment_061_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 3024 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3024 54 54, g32p_row02_traceSegment_061_3024_0054, g32p_row02_traceSegment_061_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3132 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3145 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3132 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3132 13 14, g32p_row02_traceSegment_061_3132_0013, g32p_row02_traceSegment_061_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3159 13 14, g32p_row02_traceSegment_061_3159_0013, g32p_row02_traceSegment_061_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 3132 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3132 27 27, g32p_row02_traceSegment_061_3132_0027, g32p_row02_traceSegment_061_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3186 13 14, g32p_row02_traceSegment_061_3186_0013, g32p_row02_traceSegment_061_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3213 13 14, g32p_row02_traceSegment_061_3213_0013, g32p_row02_traceSegment_061_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3186 27 27, g32p_row02_traceSegment_061_3186_0027, g32p_row02_traceSegment_061_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 3132 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3132 54 54, g32p_row02_traceSegment_061_3132_0054, g32p_row02_traceSegment_061_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 3024 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3024 108 108, g32p_row02_traceSegment_061_3024_0108, g32p_row02_traceSegment_061_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3240 13 14, g32p_row02_traceSegment_061_3240_0013, g32p_row02_traceSegment_061_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3280 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3267 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3267 13 14, g32p_row02_traceSegment_061_3267_0013, g32p_row02_traceSegment_061_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 3240 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3240 27 27, g32p_row02_traceSegment_061_3240_0027, g32p_row02_traceSegment_061_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3294 13 14, g32p_row02_traceSegment_061_3294_0013, g32p_row02_traceSegment_061_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3321 13 14, g32p_row02_traceSegment_061_3321_0013, g32p_row02_traceSegment_061_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3294 27 27, g32p_row02_traceSegment_061_3294_0027, g32p_row02_traceSegment_061_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 3240 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3240 54 54, g32p_row02_traceSegment_061_3240_0054, g32p_row02_traceSegment_061_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3348 13 14, g32p_row02_traceSegment_061_3348_0013, g32p_row02_traceSegment_061_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3375 13 14, g32p_row02_traceSegment_061_3375_0013, g32p_row02_traceSegment_061_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3348 27 27, g32p_row02_traceSegment_061_3348_0027, g32p_row02_traceSegment_061_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3402 13 14, g32p_row02_traceSegment_061_3402_0013, g32p_row02_traceSegment_061_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_061 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_061 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_061_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_061 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3429 13 14, g32p_row02_traceSegment_061_3429_0013, g32p_row02_traceSegment_061_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_061 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3402 27 27, g32p_row02_traceSegment_061_3402_0027, g32p_row02_traceSegment_061_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_061 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3348 54 54, g32p_row02_traceSegment_061_3348_0054, g32p_row02_traceSegment_061_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_061 3240 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3240 108 108, g32p_row02_traceSegment_061_3240_0108, g32p_row02_traceSegment_061_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_061_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_061 3024 432 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 3024 216 216, g32p_row02_traceSegment_061_3024_0216, g32p_row02_traceSegment_061_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_061_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_061 2592 864 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 2592 432 432, g32p_row02_traceSegment_061_2592_0432, g32p_row02_traceSegment_061_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_061_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_061 1728 1728 = [0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 1728 864 864, g32p_row02_traceSegment_061_1728_0864, g32p_row02_traceSegment_061_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_061_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_061 0 3456 = [0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_061 0 1728 1728, g32p_row02_traceSegment_061_0000_1728, g32p_row02_traceSegment_061_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_061 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 61 = [0, 0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_061_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 51) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 51) (g32p_literalTraceValue 1 51)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_051]
  decide +kernel

theorem g32p_row02_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 52) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 52) (g32p_literalTraceValue 1 52)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_052]
  decide +kernel

theorem g32p_row02_tracePolynomial_055 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 55) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 55) (g32p_literalTraceValue 1 55)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_055]
  decide +kernel

theorem g32p_row02_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 56) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 56) (g32p_literalTraceValue 1 56)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row02_traceCoefficients_056]
  decide +kernel

theorem g32p_row02_tracePolynomial_057 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 57) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 57) (g32p_literalTraceValue 1 57)
      [1, -1, 1] [-3456] = true := by
  rw [g32p_row02_traceCoefficients_057]
  decide +kernel

theorem g32p_row02_tracePolynomial_058 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 58) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 58) (g32p_literalTraceValue 1 58)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_058]
  decide +kernel

theorem g32p_row02_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 59) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 59) (g32p_literalTraceValue 1 59)
      [1, -1, 1] [0, 0, 10368, 10368] = true := by
  rw [g32p_row02_traceCoefficients_059]
  decide +kernel

theorem g32p_row02_tracePolynomial_061 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 61) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 61) (g32p_literalTraceValue 1 61)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_061]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
