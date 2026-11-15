import HodgeLean.Foundations.Program.G32PropFourSixPacked0335
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0336

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_018 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 18 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_018_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 0 13 14, g32p_row04_traceSegment_018_0000_0013, g32p_row04_traceSegment_018_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 27 13 14, g32p_row04_traceSegment_018_0027_0013, g32p_row04_traceSegment_018_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 0 27 27, g32p_row04_traceSegment_018_0000_0027, g32p_row04_traceSegment_018_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 54 13 14, g32p_row04_traceSegment_018_0054_0013, g32p_row04_traceSegment_018_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 81 13 14, g32p_row04_traceSegment_018_0081_0013, g32p_row04_traceSegment_018_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 54 27 27, g32p_row04_traceSegment_018_0054_0027, g32p_row04_traceSegment_018_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 0 54 54, g32p_row04_traceSegment_018_0000_0054, g32p_row04_traceSegment_018_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 108 13 14, g32p_row04_traceSegment_018_0108_0013, g32p_row04_traceSegment_018_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 135 13 14, g32p_row04_traceSegment_018_0135_0013, g32p_row04_traceSegment_018_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 108 27 27, g32p_row04_traceSegment_018_0108_0027, g32p_row04_traceSegment_018_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 162 13 14, g32p_row04_traceSegment_018_0162_0013, g32p_row04_traceSegment_018_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 189 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 189 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 189 13 14, g32p_row04_traceSegment_018_0189_0013, g32p_row04_traceSegment_018_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 162 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 162 27 27, g32p_row04_traceSegment_018_0162_0027, g32p_row04_traceSegment_018_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 108 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 108 54 54, g32p_row04_traceSegment_018_0108_0054, g32p_row04_traceSegment_018_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_018 0 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 0 108 108, g32p_row04_traceSegment_018_0000_0108, g32p_row04_traceSegment_018_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 216 13 14, g32p_row04_traceSegment_018_0216_0013, g32p_row04_traceSegment_018_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 243 13 14, g32p_row04_traceSegment_018_0243_0013, g32p_row04_traceSegment_018_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 216 27 27, g32p_row04_traceSegment_018_0216_0027, g32p_row04_traceSegment_018_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 270 13 14, g32p_row04_traceSegment_018_0270_0013, g32p_row04_traceSegment_018_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 297 13 14, g32p_row04_traceSegment_018_0297_0013, g32p_row04_traceSegment_018_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 270 27 27, g32p_row04_traceSegment_018_0270_0027, g32p_row04_traceSegment_018_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 216 54 54, g32p_row04_traceSegment_018_0216_0054, g32p_row04_traceSegment_018_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 324 13 14, g32p_row04_traceSegment_018_0324_0013, g32p_row04_traceSegment_018_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 351 13 14, g32p_row04_traceSegment_018_0351_0013, g32p_row04_traceSegment_018_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 324 27 27, g32p_row04_traceSegment_018_0324_0027, g32p_row04_traceSegment_018_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 378 13 14, g32p_row04_traceSegment_018_0378_0013, g32p_row04_traceSegment_018_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 405 13 14, g32p_row04_traceSegment_018_0405_0013, g32p_row04_traceSegment_018_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 378 27 27, g32p_row04_traceSegment_018_0378_0027, g32p_row04_traceSegment_018_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 324 54 54, g32p_row04_traceSegment_018_0324_0054, g32p_row04_traceSegment_018_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_018 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 216 108 108, g32p_row04_traceSegment_018_0216_0108, g32p_row04_traceSegment_018_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_018 0 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 0 216 216, g32p_row04_traceSegment_018_0000_0216, g32p_row04_traceSegment_018_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 432 13 14, g32p_row04_traceSegment_018_0432_0013, g32p_row04_traceSegment_018_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 459 13 14, g32p_row04_traceSegment_018_0459_0013, g32p_row04_traceSegment_018_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 432 27 27, g32p_row04_traceSegment_018_0432_0027, g32p_row04_traceSegment_018_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 486 13 14, g32p_row04_traceSegment_018_0486_0013, g32p_row04_traceSegment_018_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 513 13 14, g32p_row04_traceSegment_018_0513_0013, g32p_row04_traceSegment_018_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 486 27 27, g32p_row04_traceSegment_018_0486_0027, g32p_row04_traceSegment_018_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 432 54 54, g32p_row04_traceSegment_018_0432_0054, g32p_row04_traceSegment_018_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 540 13 14, g32p_row04_traceSegment_018_0540_0013, g32p_row04_traceSegment_018_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 567 13 14, g32p_row04_traceSegment_018_0567_0013, g32p_row04_traceSegment_018_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 540 27 27, g32p_row04_traceSegment_018_0540_0027, g32p_row04_traceSegment_018_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 594 13 14, g32p_row04_traceSegment_018_0594_0013, g32p_row04_traceSegment_018_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 621 13 14, g32p_row04_traceSegment_018_0621_0013, g32p_row04_traceSegment_018_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 594 27 27, g32p_row04_traceSegment_018_0594_0027, g32p_row04_traceSegment_018_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 540 54 54, g32p_row04_traceSegment_018_0540_0054, g32p_row04_traceSegment_018_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_018 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 432 108 108, g32p_row04_traceSegment_018_0432_0108, g32p_row04_traceSegment_018_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 648 13 14, g32p_row04_traceSegment_018_0648_0013, g32p_row04_traceSegment_018_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 675 13 14, g32p_row04_traceSegment_018_0675_0013, g32p_row04_traceSegment_018_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 648 27 27, g32p_row04_traceSegment_018_0648_0027, g32p_row04_traceSegment_018_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 702 13 14, g32p_row04_traceSegment_018_0702_0013, g32p_row04_traceSegment_018_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 729 13 14, g32p_row04_traceSegment_018_0729_0013, g32p_row04_traceSegment_018_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 702 27 27, g32p_row04_traceSegment_018_0702_0027, g32p_row04_traceSegment_018_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 648 54 54, g32p_row04_traceSegment_018_0648_0054, g32p_row04_traceSegment_018_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 756 13 14, g32p_row04_traceSegment_018_0756_0013, g32p_row04_traceSegment_018_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 783 13 14, g32p_row04_traceSegment_018_0783_0013, g32p_row04_traceSegment_018_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 756 27 27, g32p_row04_traceSegment_018_0756_0027, g32p_row04_traceSegment_018_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 810 13 14, g32p_row04_traceSegment_018_0810_0013, g32p_row04_traceSegment_018_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 837 13 14, g32p_row04_traceSegment_018_0837_0013, g32p_row04_traceSegment_018_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 810 27 27, g32p_row04_traceSegment_018_0810_0027, g32p_row04_traceSegment_018_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 756 54 54, g32p_row04_traceSegment_018_0756_0054, g32p_row04_traceSegment_018_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_018 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 648 108 108, g32p_row04_traceSegment_018_0648_0108, g32p_row04_traceSegment_018_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_018 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 432 216 216, g32p_row04_traceSegment_018_0432_0216, g32p_row04_traceSegment_018_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_018 0 864 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 0 432 432, g32p_row04_traceSegment_018_0000_0432, g32p_row04_traceSegment_018_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 864 13 14, g32p_row04_traceSegment_018_0864_0013, g32p_row04_traceSegment_018_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 891 13 14, g32p_row04_traceSegment_018_0891_0013, g32p_row04_traceSegment_018_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 864 27 27, g32p_row04_traceSegment_018_0864_0027, g32p_row04_traceSegment_018_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 918 13 14, g32p_row04_traceSegment_018_0918_0013, g32p_row04_traceSegment_018_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 945 13 14, g32p_row04_traceSegment_018_0945_0013, g32p_row04_traceSegment_018_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 918 27 27, g32p_row04_traceSegment_018_0918_0027, g32p_row04_traceSegment_018_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 864 54 54, g32p_row04_traceSegment_018_0864_0054, g32p_row04_traceSegment_018_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 972 13 14, g32p_row04_traceSegment_018_0972_0013, g32p_row04_traceSegment_018_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 999 13 14, g32p_row04_traceSegment_018_0999_0013, g32p_row04_traceSegment_018_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 972 27 27, g32p_row04_traceSegment_018_0972_0027, g32p_row04_traceSegment_018_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1026 13 14, g32p_row04_traceSegment_018_1026_0013, g32p_row04_traceSegment_018_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1053 13 14, g32p_row04_traceSegment_018_1053_0013, g32p_row04_traceSegment_018_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1026 27 27, g32p_row04_traceSegment_018_1026_0027, g32p_row04_traceSegment_018_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 972 54 54, g32p_row04_traceSegment_018_0972_0054, g32p_row04_traceSegment_018_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_018 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 864 108 108, g32p_row04_traceSegment_018_0864_0108, g32p_row04_traceSegment_018_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1080 13 14, g32p_row04_traceSegment_018_1080_0013, g32p_row04_traceSegment_018_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1120 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1107 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1107 13 14, g32p_row04_traceSegment_018_1107_0013, g32p_row04_traceSegment_018_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1080 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1080 27 27, g32p_row04_traceSegment_018_1080_0027, g32p_row04_traceSegment_018_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1134 13 14, g32p_row04_traceSegment_018_1134_0013, g32p_row04_traceSegment_018_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1161 13 14, g32p_row04_traceSegment_018_1161_0013, g32p_row04_traceSegment_018_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1134 27 27, g32p_row04_traceSegment_018_1134_0027, g32p_row04_traceSegment_018_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 1080 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1080 54 54, g32p_row04_traceSegment_018_1080_0054, g32p_row04_traceSegment_018_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1188 13 14, g32p_row04_traceSegment_018_1188_0013, g32p_row04_traceSegment_018_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1215 13 14, g32p_row04_traceSegment_018_1215_0013, g32p_row04_traceSegment_018_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1188 27 27, g32p_row04_traceSegment_018_1188_0027, g32p_row04_traceSegment_018_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1242 13 14, g32p_row04_traceSegment_018_1242_0013, g32p_row04_traceSegment_018_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1269 13 14, g32p_row04_traceSegment_018_1269_0013, g32p_row04_traceSegment_018_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1242 27 27, g32p_row04_traceSegment_018_1242_0027, g32p_row04_traceSegment_018_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1188 54 54, g32p_row04_traceSegment_018_1188_0054, g32p_row04_traceSegment_018_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_018 1080 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1080 108 108, g32p_row04_traceSegment_018_1080_0108, g32p_row04_traceSegment_018_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_018 864 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 864 216 216, g32p_row04_traceSegment_018_0864_0216, g32p_row04_traceSegment_018_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1296 13 14, g32p_row04_traceSegment_018_1296_0013, g32p_row04_traceSegment_018_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1323 13 14, g32p_row04_traceSegment_018_1323_0013, g32p_row04_traceSegment_018_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1296 27 27, g32p_row04_traceSegment_018_1296_0027, g32p_row04_traceSegment_018_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1350 13 14, g32p_row04_traceSegment_018_1350_0013, g32p_row04_traceSegment_018_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1377 13 14, g32p_row04_traceSegment_018_1377_0013, g32p_row04_traceSegment_018_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1350 27 27, g32p_row04_traceSegment_018_1350_0027, g32p_row04_traceSegment_018_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1296 54 54, g32p_row04_traceSegment_018_1296_0054, g32p_row04_traceSegment_018_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1404 13 14, g32p_row04_traceSegment_018_1404_0013, g32p_row04_traceSegment_018_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1431 13 14, g32p_row04_traceSegment_018_1431_0013, g32p_row04_traceSegment_018_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1404 27 27, g32p_row04_traceSegment_018_1404_0027, g32p_row04_traceSegment_018_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1458 13 14, g32p_row04_traceSegment_018_1458_0013, g32p_row04_traceSegment_018_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1485 13 14, g32p_row04_traceSegment_018_1485_0013, g32p_row04_traceSegment_018_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1458 27 27, g32p_row04_traceSegment_018_1458_0027, g32p_row04_traceSegment_018_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1404 54 54, g32p_row04_traceSegment_018_1404_0054, g32p_row04_traceSegment_018_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_018 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1296 108 108, g32p_row04_traceSegment_018_1296_0108, g32p_row04_traceSegment_018_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1512 13 14, g32p_row04_traceSegment_018_1512_0013, g32p_row04_traceSegment_018_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1539 13 14, g32p_row04_traceSegment_018_1539_0013, g32p_row04_traceSegment_018_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1512 27 27, g32p_row04_traceSegment_018_1512_0027, g32p_row04_traceSegment_018_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1566 13 14, g32p_row04_traceSegment_018_1566_0013, g32p_row04_traceSegment_018_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1593 13 14, g32p_row04_traceSegment_018_1593_0013, g32p_row04_traceSegment_018_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1566 27 27, g32p_row04_traceSegment_018_1566_0027, g32p_row04_traceSegment_018_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1512 54 54, g32p_row04_traceSegment_018_1512_0054, g32p_row04_traceSegment_018_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1620 13 14, g32p_row04_traceSegment_018_1620_0013, g32p_row04_traceSegment_018_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1647 13 14, g32p_row04_traceSegment_018_1647_0013, g32p_row04_traceSegment_018_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1620 27 27, g32p_row04_traceSegment_018_1620_0027, g32p_row04_traceSegment_018_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1674 13 14, g32p_row04_traceSegment_018_1674_0013, g32p_row04_traceSegment_018_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_018 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_018 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_018_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_018 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1701 13 14, g32p_row04_traceSegment_018_1701_0013, g32p_row04_traceSegment_018_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_018 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1674 27 27, g32p_row04_traceSegment_018_1674_0027, g32p_row04_traceSegment_018_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_018 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1620 54 54, g32p_row04_traceSegment_018_1620_0054, g32p_row04_traceSegment_018_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_018 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1512 108 108, g32p_row04_traceSegment_018_1512_0108, g32p_row04_traceSegment_018_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_018_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_018 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 1296 216 216, g32p_row04_traceSegment_018_1296_0216, g32p_row04_traceSegment_018_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_018 864 864 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 864 432 432, g32p_row04_traceSegment_018_0864_0432, g32p_row04_traceSegment_018_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_018_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_018 0 1728 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_018 0 864 864, g32p_row04_traceSegment_018_0000_0864, g32p_row04_traceSegment_018_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 18 = [2] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_018_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_019 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 19 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_019_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 0 13 14, g32p_row04_traceSegment_019_0000_0013, g32p_row04_traceSegment_019_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 27 13 14, g32p_row04_traceSegment_019_0027_0013, g32p_row04_traceSegment_019_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 0 27 27, g32p_row04_traceSegment_019_0000_0027, g32p_row04_traceSegment_019_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 54 13 14, g32p_row04_traceSegment_019_0054_0013, g32p_row04_traceSegment_019_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 81 13 14, g32p_row04_traceSegment_019_0081_0013, g32p_row04_traceSegment_019_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 54 27 27, g32p_row04_traceSegment_019_0054_0027, g32p_row04_traceSegment_019_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 0 54 54, g32p_row04_traceSegment_019_0000_0054, g32p_row04_traceSegment_019_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 108 13 14, g32p_row04_traceSegment_019_0108_0013, g32p_row04_traceSegment_019_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 135 13 14, g32p_row04_traceSegment_019_0135_0013, g32p_row04_traceSegment_019_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 108 27 27, g32p_row04_traceSegment_019_0108_0027, g32p_row04_traceSegment_019_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 162 13 14, g32p_row04_traceSegment_019_0162_0013, g32p_row04_traceSegment_019_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 189 13 14, g32p_row04_traceSegment_019_0189_0013, g32p_row04_traceSegment_019_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 162 27 27, g32p_row04_traceSegment_019_0162_0027, g32p_row04_traceSegment_019_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 108 54 54, g32p_row04_traceSegment_019_0108_0054, g32p_row04_traceSegment_019_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_019 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 0 108 108, g32p_row04_traceSegment_019_0000_0108, g32p_row04_traceSegment_019_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 216 13 14, g32p_row04_traceSegment_019_0216_0013, g32p_row04_traceSegment_019_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 243 13 14, g32p_row04_traceSegment_019_0243_0013, g32p_row04_traceSegment_019_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 216 27 27, g32p_row04_traceSegment_019_0216_0027, g32p_row04_traceSegment_019_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 270 13 14, g32p_row04_traceSegment_019_0270_0013, g32p_row04_traceSegment_019_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 297 13 14, g32p_row04_traceSegment_019_0297_0013, g32p_row04_traceSegment_019_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 270 27 27, g32p_row04_traceSegment_019_0270_0027, g32p_row04_traceSegment_019_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 216 54 54, g32p_row04_traceSegment_019_0216_0054, g32p_row04_traceSegment_019_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 324 13 14, g32p_row04_traceSegment_019_0324_0013, g32p_row04_traceSegment_019_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 351 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 351 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 351 13 14, g32p_row04_traceSegment_019_0351_0013, g32p_row04_traceSegment_019_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 324 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 324 27 27, g32p_row04_traceSegment_019_0324_0027, g32p_row04_traceSegment_019_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 378 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 378 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 378 13 14, g32p_row04_traceSegment_019_0378_0013, g32p_row04_traceSegment_019_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 405 13 14, g32p_row04_traceSegment_019_0405_0013, g32p_row04_traceSegment_019_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 378 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 378 27 27, g32p_row04_traceSegment_019_0378_0027, g32p_row04_traceSegment_019_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 324 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 324 54 54, g32p_row04_traceSegment_019_0324_0054, g32p_row04_traceSegment_019_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_019 216 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 216 108 108, g32p_row04_traceSegment_019_0216_0108, g32p_row04_traceSegment_019_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_019 0 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 0 216 216, g32p_row04_traceSegment_019_0000_0216, g32p_row04_traceSegment_019_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 432 13 14, g32p_row04_traceSegment_019_0432_0013, g32p_row04_traceSegment_019_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 472 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 459 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 459 13 14, g32p_row04_traceSegment_019_0459_0013, g32p_row04_traceSegment_019_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 432 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 432 27 27, g32p_row04_traceSegment_019_0432_0027, g32p_row04_traceSegment_019_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 486 13 14, g32p_row04_traceSegment_019_0486_0013, g32p_row04_traceSegment_019_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 513 13 14, g32p_row04_traceSegment_019_0513_0013, g32p_row04_traceSegment_019_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 486 27 27, g32p_row04_traceSegment_019_0486_0027, g32p_row04_traceSegment_019_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 432 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 432 54 54, g32p_row04_traceSegment_019_0432_0054, g32p_row04_traceSegment_019_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 540 13 14, g32p_row04_traceSegment_019_0540_0013, g32p_row04_traceSegment_019_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 567 13 14, g32p_row04_traceSegment_019_0567_0013, g32p_row04_traceSegment_019_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 540 27 27, g32p_row04_traceSegment_019_0540_0027, g32p_row04_traceSegment_019_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 594 13 14, g32p_row04_traceSegment_019_0594_0013, g32p_row04_traceSegment_019_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 621 13 14, g32p_row04_traceSegment_019_0621_0013, g32p_row04_traceSegment_019_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 594 27 27, g32p_row04_traceSegment_019_0594_0027, g32p_row04_traceSegment_019_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 540 54 54, g32p_row04_traceSegment_019_0540_0054, g32p_row04_traceSegment_019_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_019 432 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 432 108 108, g32p_row04_traceSegment_019_0432_0108, g32p_row04_traceSegment_019_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 648 13 14, g32p_row04_traceSegment_019_0648_0013, g32p_row04_traceSegment_019_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 675 13 14, g32p_row04_traceSegment_019_0675_0013, g32p_row04_traceSegment_019_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 648 27 27, g32p_row04_traceSegment_019_0648_0027, g32p_row04_traceSegment_019_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 702 13 14, g32p_row04_traceSegment_019_0702_0013, g32p_row04_traceSegment_019_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 729 13 14, g32p_row04_traceSegment_019_0729_0013, g32p_row04_traceSegment_019_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 702 27 27, g32p_row04_traceSegment_019_0702_0027, g32p_row04_traceSegment_019_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 648 54 54, g32p_row04_traceSegment_019_0648_0054, g32p_row04_traceSegment_019_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 756 13 14, g32p_row04_traceSegment_019_0756_0013, g32p_row04_traceSegment_019_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 783 13 14, g32p_row04_traceSegment_019_0783_0013, g32p_row04_traceSegment_019_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 756 27 27, g32p_row04_traceSegment_019_0756_0027, g32p_row04_traceSegment_019_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 810 13 14, g32p_row04_traceSegment_019_0810_0013, g32p_row04_traceSegment_019_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 837 13 14, g32p_row04_traceSegment_019_0837_0013, g32p_row04_traceSegment_019_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 810 27 27, g32p_row04_traceSegment_019_0810_0027, g32p_row04_traceSegment_019_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 756 54 54, g32p_row04_traceSegment_019_0756_0054, g32p_row04_traceSegment_019_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_019 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 648 108 108, g32p_row04_traceSegment_019_0648_0108, g32p_row04_traceSegment_019_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_019 432 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 432 216 216, g32p_row04_traceSegment_019_0432_0216, g32p_row04_traceSegment_019_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_019 0 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 0 432 432, g32p_row04_traceSegment_019_0000_0432, g32p_row04_traceSegment_019_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 864 13 14, g32p_row04_traceSegment_019_0864_0013, g32p_row04_traceSegment_019_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 891 13 14, g32p_row04_traceSegment_019_0891_0013, g32p_row04_traceSegment_019_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 864 27 27, g32p_row04_traceSegment_019_0864_0027, g32p_row04_traceSegment_019_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 918 13 14, g32p_row04_traceSegment_019_0918_0013, g32p_row04_traceSegment_019_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 945 13 14, g32p_row04_traceSegment_019_0945_0013, g32p_row04_traceSegment_019_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 918 27 27, g32p_row04_traceSegment_019_0918_0027, g32p_row04_traceSegment_019_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 864 54 54, g32p_row04_traceSegment_019_0864_0054, g32p_row04_traceSegment_019_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 972 13 14, g32p_row04_traceSegment_019_0972_0013, g32p_row04_traceSegment_019_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 999 13 14, g32p_row04_traceSegment_019_0999_0013, g32p_row04_traceSegment_019_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 972 27 27, g32p_row04_traceSegment_019_0972_0027, g32p_row04_traceSegment_019_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1026 13 14, g32p_row04_traceSegment_019_1026_0013, g32p_row04_traceSegment_019_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1053 13 14, g32p_row04_traceSegment_019_1053_0013, g32p_row04_traceSegment_019_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1026 27 27, g32p_row04_traceSegment_019_1026_0027, g32p_row04_traceSegment_019_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 972 54 54, g32p_row04_traceSegment_019_0972_0054, g32p_row04_traceSegment_019_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_019 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 864 108 108, g32p_row04_traceSegment_019_0864_0108, g32p_row04_traceSegment_019_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1080 13 14, g32p_row04_traceSegment_019_1080_0013, g32p_row04_traceSegment_019_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1107 13 14, g32p_row04_traceSegment_019_1107_0013, g32p_row04_traceSegment_019_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1080 27 27, g32p_row04_traceSegment_019_1080_0027, g32p_row04_traceSegment_019_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1134 13 14, g32p_row04_traceSegment_019_1134_0013, g32p_row04_traceSegment_019_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1161 13 14, g32p_row04_traceSegment_019_1161_0013, g32p_row04_traceSegment_019_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1134 27 27, g32p_row04_traceSegment_019_1134_0027, g32p_row04_traceSegment_019_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1080 54 54, g32p_row04_traceSegment_019_1080_0054, g32p_row04_traceSegment_019_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1188 13 14, g32p_row04_traceSegment_019_1188_0013, g32p_row04_traceSegment_019_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1215 13 14, g32p_row04_traceSegment_019_1215_0013, g32p_row04_traceSegment_019_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1188 27 27, g32p_row04_traceSegment_019_1188_0027, g32p_row04_traceSegment_019_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1242 13 14, g32p_row04_traceSegment_019_1242_0013, g32p_row04_traceSegment_019_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1269 13 14, g32p_row04_traceSegment_019_1269_0013, g32p_row04_traceSegment_019_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1242 27 27, g32p_row04_traceSegment_019_1242_0027, g32p_row04_traceSegment_019_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1188 54 54, g32p_row04_traceSegment_019_1188_0054, g32p_row04_traceSegment_019_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_019 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1080 108 108, g32p_row04_traceSegment_019_1080_0108, g32p_row04_traceSegment_019_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_019 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 864 216 216, g32p_row04_traceSegment_019_0864_0216, g32p_row04_traceSegment_019_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1296 13 14, g32p_row04_traceSegment_019_1296_0013, g32p_row04_traceSegment_019_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1323 13 14, g32p_row04_traceSegment_019_1323_0013, g32p_row04_traceSegment_019_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1296 27 27, g32p_row04_traceSegment_019_1296_0027, g32p_row04_traceSegment_019_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1350 13 14, g32p_row04_traceSegment_019_1350_0013, g32p_row04_traceSegment_019_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1377 13 14, g32p_row04_traceSegment_019_1377_0013, g32p_row04_traceSegment_019_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1350 27 27, g32p_row04_traceSegment_019_1350_0027, g32p_row04_traceSegment_019_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1296 54 54, g32p_row04_traceSegment_019_1296_0054, g32p_row04_traceSegment_019_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1417 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1404 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1404 13 14, g32p_row04_traceSegment_019_1404_0013, g32p_row04_traceSegment_019_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1431 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1431 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1431 13 14, g32p_row04_traceSegment_019_1431_0013, g32p_row04_traceSegment_019_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1404 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1404 27 27, g32p_row04_traceSegment_019_1404_0027, g32p_row04_traceSegment_019_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1471 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1458 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1458 13 14, g32p_row04_traceSegment_019_1458_0013, g32p_row04_traceSegment_019_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1485 13 14, g32p_row04_traceSegment_019_1485_0013, g32p_row04_traceSegment_019_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1458 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1458 27 27, g32p_row04_traceSegment_019_1458_0027, g32p_row04_traceSegment_019_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 1404 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1404 54 54, g32p_row04_traceSegment_019_1404_0054, g32p_row04_traceSegment_019_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_019 1296 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1296 108 108, g32p_row04_traceSegment_019_1296_0108, g32p_row04_traceSegment_019_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1512 13 14, g32p_row04_traceSegment_019_1512_0013, g32p_row04_traceSegment_019_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1539 13 14, g32p_row04_traceSegment_019_1539_0013, g32p_row04_traceSegment_019_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1512 27 27, g32p_row04_traceSegment_019_1512_0027, g32p_row04_traceSegment_019_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1566 13 14, g32p_row04_traceSegment_019_1566_0013, g32p_row04_traceSegment_019_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1593 13 14, g32p_row04_traceSegment_019_1593_0013, g32p_row04_traceSegment_019_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1566 27 27, g32p_row04_traceSegment_019_1566_0027, g32p_row04_traceSegment_019_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1512 54 54, g32p_row04_traceSegment_019_1512_0054, g32p_row04_traceSegment_019_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1620 13 14, g32p_row04_traceSegment_019_1620_0013, g32p_row04_traceSegment_019_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1647 13 14, g32p_row04_traceSegment_019_1647_0013, g32p_row04_traceSegment_019_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1620 27 27, g32p_row04_traceSegment_019_1620_0027, g32p_row04_traceSegment_019_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1674 13 14, g32p_row04_traceSegment_019_1674_0013, g32p_row04_traceSegment_019_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_019 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_019 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_019_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_019 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1701 13 14, g32p_row04_traceSegment_019_1701_0013, g32p_row04_traceSegment_019_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_019 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1674 27 27, g32p_row04_traceSegment_019_1674_0027, g32p_row04_traceSegment_019_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_019 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1620 54 54, g32p_row04_traceSegment_019_1620_0054, g32p_row04_traceSegment_019_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_019 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1512 108 108, g32p_row04_traceSegment_019_1512_0108, g32p_row04_traceSegment_019_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_019_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_019 1296 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 1296 216 216, g32p_row04_traceSegment_019_1296_0216, g32p_row04_traceSegment_019_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_019 864 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 864 432 432, g32p_row04_traceSegment_019_0864_0432, g32p_row04_traceSegment_019_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_019_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_019 0 1728 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_019 0 864 864, g32p_row04_traceSegment_019_0000_0864, g32p_row04_traceSegment_019_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 19 = [4, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_019_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 8) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 8) (g32p_literalTraceValue 3 8)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_008]
  decide +kernel

theorem g32p_row04_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 10) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 10) (g32p_literalTraceValue 3 10)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_010]
  decide +kernel

theorem g32p_row04_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 11) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 11) (g32p_literalTraceValue 3 11)
      [1, 1, 1] [10368] = true := by
  rw [g32p_row04_traceCoefficients_011]
  decide +kernel

theorem g32p_row04_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 13) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 13) (g32p_literalTraceValue 3 13)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_013]
  decide +kernel

theorem g32p_row04_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 15) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 15) (g32p_literalTraceValue 3 15)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_015]
  decide +kernel

theorem g32p_row04_tracePolynomial_017 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 17) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 17) (g32p_literalTraceValue 3 17)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_017]
  decide +kernel

theorem g32p_row04_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 18) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 18) (g32p_literalTraceValue 3 18)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_018]
  decide +kernel

theorem g32p_row04_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 19) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 19) (g32p_literalTraceValue 3 19)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_019]
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

private def g32p_row04_traceSegment_020 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 20 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_020_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 0 13 14, g32p_row04_traceSegment_020_0000_0013, g32p_row04_traceSegment_020_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 40 14 = [4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 27 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 27 13 14, g32p_row04_traceSegment_020_0027_0013, g32p_row04_traceSegment_020_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 0 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 0 27 27, g32p_row04_traceSegment_020_0000_0027, g32p_row04_traceSegment_020_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 54 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 54 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 54 13 14, g32p_row04_traceSegment_020_0054_0013, g32p_row04_traceSegment_020_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 81 13 14, g32p_row04_traceSegment_020_0081_0013, g32p_row04_traceSegment_020_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 54 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 54 27 27, g32p_row04_traceSegment_020_0054_0027, g32p_row04_traceSegment_020_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 0 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 0 54 54, g32p_row04_traceSegment_020_0000_0054, g32p_row04_traceSegment_020_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 108 13 14, g32p_row04_traceSegment_020_0108_0013, g32p_row04_traceSegment_020_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 135 13 14, g32p_row04_traceSegment_020_0135_0013, g32p_row04_traceSegment_020_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 108 27 27, g32p_row04_traceSegment_020_0108_0027, g32p_row04_traceSegment_020_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 162 13 14, g32p_row04_traceSegment_020_0162_0013, g32p_row04_traceSegment_020_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 189 13 14, g32p_row04_traceSegment_020_0189_0013, g32p_row04_traceSegment_020_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 162 27 27, g32p_row04_traceSegment_020_0162_0027, g32p_row04_traceSegment_020_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 108 54 54, g32p_row04_traceSegment_020_0108_0054, g32p_row04_traceSegment_020_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_020 0 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 0 108 108, g32p_row04_traceSegment_020_0000_0108, g32p_row04_traceSegment_020_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 216 13 14, g32p_row04_traceSegment_020_0216_0013, g32p_row04_traceSegment_020_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 243 13 14, g32p_row04_traceSegment_020_0243_0013, g32p_row04_traceSegment_020_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 216 27 27, g32p_row04_traceSegment_020_0216_0027, g32p_row04_traceSegment_020_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 283 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 270 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 270 13 14, g32p_row04_traceSegment_020_0270_0013, g32p_row04_traceSegment_020_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 297 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 297 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 297 13 14, g32p_row04_traceSegment_020_0297_0013, g32p_row04_traceSegment_020_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 270 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 270 27 27, g32p_row04_traceSegment_020_0270_0027, g32p_row04_traceSegment_020_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 216 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 216 54 54, g32p_row04_traceSegment_020_0216_0054, g32p_row04_traceSegment_020_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 337 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 324 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 324 13 14, g32p_row04_traceSegment_020_0324_0013, g32p_row04_traceSegment_020_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 364 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 351 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 351 13 14, g32p_row04_traceSegment_020_0351_0013, g32p_row04_traceSegment_020_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 324 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 324 27 27, g32p_row04_traceSegment_020_0324_0027, g32p_row04_traceSegment_020_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 378 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 378 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 378 13 14, g32p_row04_traceSegment_020_0378_0013, g32p_row04_traceSegment_020_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 405 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 418 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 405 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 405 13 14, g32p_row04_traceSegment_020_0405_0013, g32p_row04_traceSegment_020_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 378 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 378 27 27, g32p_row04_traceSegment_020_0378_0027, g32p_row04_traceSegment_020_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 324 108 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 324 54 54, g32p_row04_traceSegment_020_0324_0054, g32p_row04_traceSegment_020_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_020 216 216 = [2, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 216 108 108, g32p_row04_traceSegment_020_0216_0108, g32p_row04_traceSegment_020_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_020 0 432 = [8, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 0 216 216, g32p_row04_traceSegment_020_0000_0216, g32p_row04_traceSegment_020_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 445 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 432 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 432 13 14, g32p_row04_traceSegment_020_0432_0013, g32p_row04_traceSegment_020_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 459 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 459 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 459 13 14, g32p_row04_traceSegment_020_0459_0013, g32p_row04_traceSegment_020_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 432 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 432 27 27, g32p_row04_traceSegment_020_0432_0027, g32p_row04_traceSegment_020_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 486 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 486 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 486 13 14, g32p_row04_traceSegment_020_0486_0013, g32p_row04_traceSegment_020_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 513 13 14, g32p_row04_traceSegment_020_0513_0013, g32p_row04_traceSegment_020_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 486 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 486 27 27, g32p_row04_traceSegment_020_0486_0027, g32p_row04_traceSegment_020_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 432 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 432 54 54, g32p_row04_traceSegment_020_0432_0054, g32p_row04_traceSegment_020_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 540 13 14, g32p_row04_traceSegment_020_0540_0013, g32p_row04_traceSegment_020_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 567 13 14, g32p_row04_traceSegment_020_0567_0013, g32p_row04_traceSegment_020_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 540 27 27, g32p_row04_traceSegment_020_0540_0027, g32p_row04_traceSegment_020_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 594 13 14, g32p_row04_traceSegment_020_0594_0013, g32p_row04_traceSegment_020_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 621 13 14, g32p_row04_traceSegment_020_0621_0013, g32p_row04_traceSegment_020_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 594 27 27, g32p_row04_traceSegment_020_0594_0027, g32p_row04_traceSegment_020_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 540 54 54, g32p_row04_traceSegment_020_0540_0054, g32p_row04_traceSegment_020_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_020 432 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 432 108 108, g32p_row04_traceSegment_020_0432_0108, g32p_row04_traceSegment_020_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 648 13 14, g32p_row04_traceSegment_020_0648_0013, g32p_row04_traceSegment_020_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 675 13 14, g32p_row04_traceSegment_020_0675_0013, g32p_row04_traceSegment_020_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 648 27 27, g32p_row04_traceSegment_020_0648_0027, g32p_row04_traceSegment_020_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 702 13 14, g32p_row04_traceSegment_020_0702_0013, g32p_row04_traceSegment_020_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 729 13 14, g32p_row04_traceSegment_020_0729_0013, g32p_row04_traceSegment_020_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 702 27 27, g32p_row04_traceSegment_020_0702_0027, g32p_row04_traceSegment_020_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 648 54 54, g32p_row04_traceSegment_020_0648_0054, g32p_row04_traceSegment_020_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 756 13 14, g32p_row04_traceSegment_020_0756_0013, g32p_row04_traceSegment_020_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 783 13 14, g32p_row04_traceSegment_020_0783_0013, g32p_row04_traceSegment_020_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 756 27 27, g32p_row04_traceSegment_020_0756_0027, g32p_row04_traceSegment_020_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 810 13 14, g32p_row04_traceSegment_020_0810_0013, g32p_row04_traceSegment_020_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 837 13 14, g32p_row04_traceSegment_020_0837_0013, g32p_row04_traceSegment_020_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 810 27 27, g32p_row04_traceSegment_020_0810_0027, g32p_row04_traceSegment_020_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 756 54 54, g32p_row04_traceSegment_020_0756_0054, g32p_row04_traceSegment_020_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_020 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 648 108 108, g32p_row04_traceSegment_020_0648_0108, g32p_row04_traceSegment_020_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_020 432 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 432 216 216, g32p_row04_traceSegment_020_0432_0216, g32p_row04_traceSegment_020_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_020 0 864 = [11, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 0 432 432, g32p_row04_traceSegment_020_0000_0432, g32p_row04_traceSegment_020_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 864 13 14, g32p_row04_traceSegment_020_0864_0013, g32p_row04_traceSegment_020_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 891 13 14, g32p_row04_traceSegment_020_0891_0013, g32p_row04_traceSegment_020_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 864 27 27, g32p_row04_traceSegment_020_0864_0027, g32p_row04_traceSegment_020_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 918 13 14, g32p_row04_traceSegment_020_0918_0013, g32p_row04_traceSegment_020_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 945 13 14, g32p_row04_traceSegment_020_0945_0013, g32p_row04_traceSegment_020_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 918 27 27, g32p_row04_traceSegment_020_0918_0027, g32p_row04_traceSegment_020_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 864 54 54, g32p_row04_traceSegment_020_0864_0054, g32p_row04_traceSegment_020_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 972 13 14, g32p_row04_traceSegment_020_0972_0013, g32p_row04_traceSegment_020_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 999 13 14, g32p_row04_traceSegment_020_0999_0013, g32p_row04_traceSegment_020_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 972 27 27, g32p_row04_traceSegment_020_0972_0027, g32p_row04_traceSegment_020_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1026 13 14, g32p_row04_traceSegment_020_1026_0013, g32p_row04_traceSegment_020_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1053 13 14, g32p_row04_traceSegment_020_1053_0013, g32p_row04_traceSegment_020_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1026 27 27, g32p_row04_traceSegment_020_1026_0027, g32p_row04_traceSegment_020_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 972 54 54, g32p_row04_traceSegment_020_0972_0054, g32p_row04_traceSegment_020_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_020 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 864 108 108, g32p_row04_traceSegment_020_0864_0108, g32p_row04_traceSegment_020_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1080 13 14, g32p_row04_traceSegment_020_1080_0013, g32p_row04_traceSegment_020_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1107 13 14, g32p_row04_traceSegment_020_1107_0013, g32p_row04_traceSegment_020_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1080 27 27, g32p_row04_traceSegment_020_1080_0027, g32p_row04_traceSegment_020_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1134 13 14, g32p_row04_traceSegment_020_1134_0013, g32p_row04_traceSegment_020_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1161 13 14, g32p_row04_traceSegment_020_1161_0013, g32p_row04_traceSegment_020_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1134 27 27, g32p_row04_traceSegment_020_1134_0027, g32p_row04_traceSegment_020_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1080 54 54, g32p_row04_traceSegment_020_1080_0054, g32p_row04_traceSegment_020_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1188 13 14, g32p_row04_traceSegment_020_1188_0013, g32p_row04_traceSegment_020_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1228 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1215 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1215 13 14, g32p_row04_traceSegment_020_1215_0013, g32p_row04_traceSegment_020_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1188 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1188 27 27, g32p_row04_traceSegment_020_1188_0027, g32p_row04_traceSegment_020_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1242 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1255 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1242 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1242 13 14, g32p_row04_traceSegment_020_1242_0013, g32p_row04_traceSegment_020_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1269 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1269 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1269 13 14, g32p_row04_traceSegment_020_1269_0013, g32p_row04_traceSegment_020_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1242 54 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1242 27 27, g32p_row04_traceSegment_020_1242_0027, g32p_row04_traceSegment_020_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 1188 108 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1188 54 54, g32p_row04_traceSegment_020_1188_0054, g32p_row04_traceSegment_020_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_020 1080 216 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1080 108 108, g32p_row04_traceSegment_020_1080_0108, g32p_row04_traceSegment_020_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_020 864 432 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 864 216 216, g32p_row04_traceSegment_020_0864_0216, g32p_row04_traceSegment_020_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1296 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1296 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1296 13 14, g32p_row04_traceSegment_020_1296_0013, g32p_row04_traceSegment_020_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1323 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1323 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1323 13 14, g32p_row04_traceSegment_020_1323_0013, g32p_row04_traceSegment_020_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1296 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1296 27 27, g32p_row04_traceSegment_020_1296_0027, g32p_row04_traceSegment_020_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1350 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1363 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1350 27 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1350 13 14, g32p_row04_traceSegment_020_1350_0013, g32p_row04_traceSegment_020_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1377 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1390 14 = [4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1377 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1377 13 14, g32p_row04_traceSegment_020_1377_0013, g32p_row04_traceSegment_020_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1350 54 = [11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1350 27 27, g32p_row04_traceSegment_020_1350_0027, g32p_row04_traceSegment_020_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 1296 108 = [13] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1296 54 54, g32p_row04_traceSegment_020_1296_0054, g32p_row04_traceSegment_020_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1404 13 14, g32p_row04_traceSegment_020_1404_0013, g32p_row04_traceSegment_020_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1431 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1444 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1431 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1431 13 14, g32p_row04_traceSegment_020_1431_0013, g32p_row04_traceSegment_020_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1404 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1404 27 27, g32p_row04_traceSegment_020_1404_0027, g32p_row04_traceSegment_020_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1458 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1471 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1458 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1458 13 14, g32p_row04_traceSegment_020_1458_0013, g32p_row04_traceSegment_020_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1485 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1498 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1485 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1485 13 14, g32p_row04_traceSegment_020_1485_0013, g32p_row04_traceSegment_020_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1458 54 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1458 27 27, g32p_row04_traceSegment_020_1458_0027, g32p_row04_traceSegment_020_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 1404 108 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1404 54 54, g32p_row04_traceSegment_020_1404_0054, g32p_row04_traceSegment_020_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_020 1296 216 = [13, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1296 108 108, g32p_row04_traceSegment_020_1296_0108, g32p_row04_traceSegment_020_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1512 13 14, g32p_row04_traceSegment_020_1512_0013, g32p_row04_traceSegment_020_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1539 13 14, g32p_row04_traceSegment_020_1539_0013, g32p_row04_traceSegment_020_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1512 27 27, g32p_row04_traceSegment_020_1512_0027, g32p_row04_traceSegment_020_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1566 13 14, g32p_row04_traceSegment_020_1566_0013, g32p_row04_traceSegment_020_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1593 13 14, g32p_row04_traceSegment_020_1593_0013, g32p_row04_traceSegment_020_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1566 27 27, g32p_row04_traceSegment_020_1566_0027, g32p_row04_traceSegment_020_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1512 54 54, g32p_row04_traceSegment_020_1512_0054, g32p_row04_traceSegment_020_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1620 13 14, g32p_row04_traceSegment_020_1620_0013, g32p_row04_traceSegment_020_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1647 13 14, g32p_row04_traceSegment_020_1647_0013, g32p_row04_traceSegment_020_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1620 27 27, g32p_row04_traceSegment_020_1620_0027, g32p_row04_traceSegment_020_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1674 13 14, g32p_row04_traceSegment_020_1674_0013, g32p_row04_traceSegment_020_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_020 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_020 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_020_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_020 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1701 13 14, g32p_row04_traceSegment_020_1701_0013, g32p_row04_traceSegment_020_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_020 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1674 27 27, g32p_row04_traceSegment_020_1674_0027, g32p_row04_traceSegment_020_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_020 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1620 54 54, g32p_row04_traceSegment_020_1620_0054, g32p_row04_traceSegment_020_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_020 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1512 108 108, g32p_row04_traceSegment_020_1512_0108, g32p_row04_traceSegment_020_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_020_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_020 1296 432 = [13, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 1296 216 216, g32p_row04_traceSegment_020_1296_0216, g32p_row04_traceSegment_020_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_020 864 864 = [13, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 864 432 432, g32p_row04_traceSegment_020_0864_0432, g32p_row04_traceSegment_020_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_020_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_020 0 1728 = [24, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_020 0 864 864, g32p_row04_traceSegment_020_0000_0864, g32p_row04_traceSegment_020_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 20 = [24, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_020_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_023 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 23 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_023_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 0 13 14, g32p_row04_traceSegment_023_0000_0013, g32p_row04_traceSegment_023_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 27 13 14, g32p_row04_traceSegment_023_0027_0013, g32p_row04_traceSegment_023_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 0 27 27, g32p_row04_traceSegment_023_0000_0027, g32p_row04_traceSegment_023_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 54 13 14, g32p_row04_traceSegment_023_0054_0013, g32p_row04_traceSegment_023_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 81 13 14, g32p_row04_traceSegment_023_0081_0013, g32p_row04_traceSegment_023_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 54 27 27, g32p_row04_traceSegment_023_0054_0027, g32p_row04_traceSegment_023_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 0 54 54, g32p_row04_traceSegment_023_0000_0054, g32p_row04_traceSegment_023_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 108 13 14, g32p_row04_traceSegment_023_0108_0013, g32p_row04_traceSegment_023_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 135 13 14, g32p_row04_traceSegment_023_0135_0013, g32p_row04_traceSegment_023_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 108 27 27, g32p_row04_traceSegment_023_0108_0027, g32p_row04_traceSegment_023_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 162 13 14, g32p_row04_traceSegment_023_0162_0013, g32p_row04_traceSegment_023_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 189 13 14, g32p_row04_traceSegment_023_0189_0013, g32p_row04_traceSegment_023_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 162 27 27, g32p_row04_traceSegment_023_0162_0027, g32p_row04_traceSegment_023_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 108 54 54, g32p_row04_traceSegment_023_0108_0054, g32p_row04_traceSegment_023_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_023 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 0 108 108, g32p_row04_traceSegment_023_0000_0108, g32p_row04_traceSegment_023_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 216 13 14, g32p_row04_traceSegment_023_0216_0013, g32p_row04_traceSegment_023_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 243 13 14, g32p_row04_traceSegment_023_0243_0013, g32p_row04_traceSegment_023_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 216 27 27, g32p_row04_traceSegment_023_0216_0027, g32p_row04_traceSegment_023_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 270 13 14, g32p_row04_traceSegment_023_0270_0013, g32p_row04_traceSegment_023_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 297 13 14, g32p_row04_traceSegment_023_0297_0013, g32p_row04_traceSegment_023_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 270 27 27, g32p_row04_traceSegment_023_0270_0027, g32p_row04_traceSegment_023_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 216 54 54, g32p_row04_traceSegment_023_0216_0054, g32p_row04_traceSegment_023_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 324 13 14, g32p_row04_traceSegment_023_0324_0013, g32p_row04_traceSegment_023_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 351 13 14, g32p_row04_traceSegment_023_0351_0013, g32p_row04_traceSegment_023_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 324 27 27, g32p_row04_traceSegment_023_0324_0027, g32p_row04_traceSegment_023_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 378 13 14, g32p_row04_traceSegment_023_0378_0013, g32p_row04_traceSegment_023_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 405 13 14, g32p_row04_traceSegment_023_0405_0013, g32p_row04_traceSegment_023_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 378 27 27, g32p_row04_traceSegment_023_0378_0027, g32p_row04_traceSegment_023_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 324 54 54, g32p_row04_traceSegment_023_0324_0054, g32p_row04_traceSegment_023_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_023 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 216 108 108, g32p_row04_traceSegment_023_0216_0108, g32p_row04_traceSegment_023_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_023 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 0 216 216, g32p_row04_traceSegment_023_0000_0216, g32p_row04_traceSegment_023_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 432 13 14, g32p_row04_traceSegment_023_0432_0013, g32p_row04_traceSegment_023_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 459 13 14, g32p_row04_traceSegment_023_0459_0013, g32p_row04_traceSegment_023_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 432 27 27, g32p_row04_traceSegment_023_0432_0027, g32p_row04_traceSegment_023_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 486 13 14, g32p_row04_traceSegment_023_0486_0013, g32p_row04_traceSegment_023_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 526 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 513 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 513 13 14, g32p_row04_traceSegment_023_0513_0013, g32p_row04_traceSegment_023_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 486 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 486 27 27, g32p_row04_traceSegment_023_0486_0027, g32p_row04_traceSegment_023_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 432 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 432 54 54, g32p_row04_traceSegment_023_0432_0054, g32p_row04_traceSegment_023_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 540 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 540 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 540 13 14, g32p_row04_traceSegment_023_0540_0013, g32p_row04_traceSegment_023_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 567 13 14, g32p_row04_traceSegment_023_0567_0013, g32p_row04_traceSegment_023_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 540 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 540 27 27, g32p_row04_traceSegment_023_0540_0027, g32p_row04_traceSegment_023_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 594 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 594 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 594 13 14, g32p_row04_traceSegment_023_0594_0013, g32p_row04_traceSegment_023_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 621 13 14, g32p_row04_traceSegment_023_0621_0013, g32p_row04_traceSegment_023_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 594 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 594 27 27, g32p_row04_traceSegment_023_0594_0027, g32p_row04_traceSegment_023_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 540 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 540 54 54, g32p_row04_traceSegment_023_0540_0054, g32p_row04_traceSegment_023_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_023 432 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 432 108 108, g32p_row04_traceSegment_023_0432_0108, g32p_row04_traceSegment_023_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 648 13 14, g32p_row04_traceSegment_023_0648_0013, g32p_row04_traceSegment_023_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 675 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 688 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 675 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 675 13 14, g32p_row04_traceSegment_023_0675_0013, g32p_row04_traceSegment_023_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 648 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 648 27 27, g32p_row04_traceSegment_023_0648_0027, g32p_row04_traceSegment_023_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 702 13 14, g32p_row04_traceSegment_023_0702_0013, g32p_row04_traceSegment_023_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 729 13 14, g32p_row04_traceSegment_023_0729_0013, g32p_row04_traceSegment_023_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 702 27 27, g32p_row04_traceSegment_023_0702_0027, g32p_row04_traceSegment_023_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 648 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 648 54 54, g32p_row04_traceSegment_023_0648_0054, g32p_row04_traceSegment_023_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 756 13 14, g32p_row04_traceSegment_023_0756_0013, g32p_row04_traceSegment_023_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 783 13 14, g32p_row04_traceSegment_023_0783_0013, g32p_row04_traceSegment_023_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 756 27 27, g32p_row04_traceSegment_023_0756_0027, g32p_row04_traceSegment_023_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 810 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 810 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 810 13 14, g32p_row04_traceSegment_023_0810_0013, g32p_row04_traceSegment_023_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 837 13 14, g32p_row04_traceSegment_023_0837_0013, g32p_row04_traceSegment_023_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 810 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 810 27 27, g32p_row04_traceSegment_023_0810_0027, g32p_row04_traceSegment_023_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 756 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 756 54 54, g32p_row04_traceSegment_023_0756_0054, g32p_row04_traceSegment_023_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_023 648 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 648 108 108, g32p_row04_traceSegment_023_0648_0108, g32p_row04_traceSegment_023_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_023 432 432 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 432 216 216, g32p_row04_traceSegment_023_0432_0216, g32p_row04_traceSegment_023_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_023 0 864 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 0 432 432, g32p_row04_traceSegment_023_0000_0432, g32p_row04_traceSegment_023_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 864 13 14, g32p_row04_traceSegment_023_0864_0013, g32p_row04_traceSegment_023_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 891 13 14, g32p_row04_traceSegment_023_0891_0013, g32p_row04_traceSegment_023_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 864 27 27, g32p_row04_traceSegment_023_0864_0027, g32p_row04_traceSegment_023_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 918 13 14, g32p_row04_traceSegment_023_0918_0013, g32p_row04_traceSegment_023_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 945 13 14, g32p_row04_traceSegment_023_0945_0013, g32p_row04_traceSegment_023_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 918 27 27, g32p_row04_traceSegment_023_0918_0027, g32p_row04_traceSegment_023_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 864 54 54, g32p_row04_traceSegment_023_0864_0054, g32p_row04_traceSegment_023_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 972 13 14, g32p_row04_traceSegment_023_0972_0013, g32p_row04_traceSegment_023_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 999 13 14, g32p_row04_traceSegment_023_0999_0013, g32p_row04_traceSegment_023_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 972 27 27, g32p_row04_traceSegment_023_0972_0027, g32p_row04_traceSegment_023_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1026 13 14, g32p_row04_traceSegment_023_1026_0013, g32p_row04_traceSegment_023_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1053 13 14, g32p_row04_traceSegment_023_1053_0013, g32p_row04_traceSegment_023_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1026 27 27, g32p_row04_traceSegment_023_1026_0027, g32p_row04_traceSegment_023_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 972 54 54, g32p_row04_traceSegment_023_0972_0054, g32p_row04_traceSegment_023_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_023 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 864 108 108, g32p_row04_traceSegment_023_0864_0108, g32p_row04_traceSegment_023_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1080 13 14, g32p_row04_traceSegment_023_1080_0013, g32p_row04_traceSegment_023_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1107 13 14, g32p_row04_traceSegment_023_1107_0013, g32p_row04_traceSegment_023_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1080 27 27, g32p_row04_traceSegment_023_1080_0027, g32p_row04_traceSegment_023_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1134 13 14, g32p_row04_traceSegment_023_1134_0013, g32p_row04_traceSegment_023_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1161 13 14, g32p_row04_traceSegment_023_1161_0013, g32p_row04_traceSegment_023_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1134 27 27, g32p_row04_traceSegment_023_1134_0027, g32p_row04_traceSegment_023_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1080 54 54, g32p_row04_traceSegment_023_1080_0054, g32p_row04_traceSegment_023_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1188 13 14, g32p_row04_traceSegment_023_1188_0013, g32p_row04_traceSegment_023_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1215 13 14, g32p_row04_traceSegment_023_1215_0013, g32p_row04_traceSegment_023_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1188 27 27, g32p_row04_traceSegment_023_1188_0027, g32p_row04_traceSegment_023_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1242 13 14, g32p_row04_traceSegment_023_1242_0013, g32p_row04_traceSegment_023_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1269 13 14, g32p_row04_traceSegment_023_1269_0013, g32p_row04_traceSegment_023_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1242 27 27, g32p_row04_traceSegment_023_1242_0027, g32p_row04_traceSegment_023_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1188 54 54, g32p_row04_traceSegment_023_1188_0054, g32p_row04_traceSegment_023_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_023 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1080 108 108, g32p_row04_traceSegment_023_1080_0108, g32p_row04_traceSegment_023_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_023 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 864 216 216, g32p_row04_traceSegment_023_0864_0216, g32p_row04_traceSegment_023_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1296 13 14, g32p_row04_traceSegment_023_1296_0013, g32p_row04_traceSegment_023_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1323 13 14, g32p_row04_traceSegment_023_1323_0013, g32p_row04_traceSegment_023_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1296 27 27, g32p_row04_traceSegment_023_1296_0027, g32p_row04_traceSegment_023_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1350 13 14, g32p_row04_traceSegment_023_1350_0013, g32p_row04_traceSegment_023_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1377 13 14, g32p_row04_traceSegment_023_1377_0013, g32p_row04_traceSegment_023_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1350 27 27, g32p_row04_traceSegment_023_1350_0027, g32p_row04_traceSegment_023_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1296 54 54, g32p_row04_traceSegment_023_1296_0054, g32p_row04_traceSegment_023_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1404 13 14, g32p_row04_traceSegment_023_1404_0013, g32p_row04_traceSegment_023_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1431 13 14, g32p_row04_traceSegment_023_1431_0013, g32p_row04_traceSegment_023_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1404 27 27, g32p_row04_traceSegment_023_1404_0027, g32p_row04_traceSegment_023_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1458 13 14, g32p_row04_traceSegment_023_1458_0013, g32p_row04_traceSegment_023_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1485 13 14, g32p_row04_traceSegment_023_1485_0013, g32p_row04_traceSegment_023_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1458 27 27, g32p_row04_traceSegment_023_1458_0027, g32p_row04_traceSegment_023_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1404 54 54, g32p_row04_traceSegment_023_1404_0054, g32p_row04_traceSegment_023_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_023 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1296 108 108, g32p_row04_traceSegment_023_1296_0108, g32p_row04_traceSegment_023_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1512 13 14, g32p_row04_traceSegment_023_1512_0013, g32p_row04_traceSegment_023_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1539 13 14, g32p_row04_traceSegment_023_1539_0013, g32p_row04_traceSegment_023_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1512 27 27, g32p_row04_traceSegment_023_1512_0027, g32p_row04_traceSegment_023_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1566 13 14, g32p_row04_traceSegment_023_1566_0013, g32p_row04_traceSegment_023_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1593 13 14, g32p_row04_traceSegment_023_1593_0013, g32p_row04_traceSegment_023_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1566 27 27, g32p_row04_traceSegment_023_1566_0027, g32p_row04_traceSegment_023_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1512 54 54, g32p_row04_traceSegment_023_1512_0054, g32p_row04_traceSegment_023_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1620 13 14, g32p_row04_traceSegment_023_1620_0013, g32p_row04_traceSegment_023_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1647 13 14, g32p_row04_traceSegment_023_1647_0013, g32p_row04_traceSegment_023_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1620 27 27, g32p_row04_traceSegment_023_1620_0027, g32p_row04_traceSegment_023_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1674 13 14, g32p_row04_traceSegment_023_1674_0013, g32p_row04_traceSegment_023_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_023 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_023 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_023_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_023 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1701 13 14, g32p_row04_traceSegment_023_1701_0013, g32p_row04_traceSegment_023_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_023 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1674 27 27, g32p_row04_traceSegment_023_1674_0027, g32p_row04_traceSegment_023_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_023 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1620 54 54, g32p_row04_traceSegment_023_1620_0054, g32p_row04_traceSegment_023_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_023 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1512 108 108, g32p_row04_traceSegment_023_1512_0108, g32p_row04_traceSegment_023_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_023_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_023 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 1296 216 216, g32p_row04_traceSegment_023_1296_0216, g32p_row04_traceSegment_023_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_023 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 864 432 432, g32p_row04_traceSegment_023_0864_0432, g32p_row04_traceSegment_023_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_023_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_023 0 1728 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_023 0 864 864, g32p_row04_traceSegment_023_0000_0864, g32p_row04_traceSegment_023_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 23 = [4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_023_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_024 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 24 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_024_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 0 13 14, g32p_row04_traceSegment_024_0000_0013, g32p_row04_traceSegment_024_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 27 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 27 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 27 13 14, g32p_row04_traceSegment_024_0027_0013, g32p_row04_traceSegment_024_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 0 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 0 27 27, g32p_row04_traceSegment_024_0000_0027, g32p_row04_traceSegment_024_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 54 13 14, g32p_row04_traceSegment_024_0054_0013, g32p_row04_traceSegment_024_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 81 13 14, g32p_row04_traceSegment_024_0081_0013, g32p_row04_traceSegment_024_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 54 27 27, g32p_row04_traceSegment_024_0054_0027, g32p_row04_traceSegment_024_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 0 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 0 54 54, g32p_row04_traceSegment_024_0000_0054, g32p_row04_traceSegment_024_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 108 13 14, g32p_row04_traceSegment_024_0108_0013, g32p_row04_traceSegment_024_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 135 13 14, g32p_row04_traceSegment_024_0135_0013, g32p_row04_traceSegment_024_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 108 27 27, g32p_row04_traceSegment_024_0108_0027, g32p_row04_traceSegment_024_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 162 13 14, g32p_row04_traceSegment_024_0162_0013, g32p_row04_traceSegment_024_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 189 13 14, g32p_row04_traceSegment_024_0189_0013, g32p_row04_traceSegment_024_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 162 27 27, g32p_row04_traceSegment_024_0162_0027, g32p_row04_traceSegment_024_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 108 54 54, g32p_row04_traceSegment_024_0108_0054, g32p_row04_traceSegment_024_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_024 0 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 0 108 108, g32p_row04_traceSegment_024_0000_0108, g32p_row04_traceSegment_024_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 216 13 14, g32p_row04_traceSegment_024_0216_0013, g32p_row04_traceSegment_024_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 243 13 14, g32p_row04_traceSegment_024_0243_0013, g32p_row04_traceSegment_024_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 216 27 27, g32p_row04_traceSegment_024_0216_0027, g32p_row04_traceSegment_024_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 270 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 270 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 270 13 14, g32p_row04_traceSegment_024_0270_0013, g32p_row04_traceSegment_024_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 297 13 14, g32p_row04_traceSegment_024_0297_0013, g32p_row04_traceSegment_024_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 270 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 270 27 27, g32p_row04_traceSegment_024_0270_0027, g32p_row04_traceSegment_024_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 216 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 216 54 54, g32p_row04_traceSegment_024_0216_0054, g32p_row04_traceSegment_024_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 324 13 14, g32p_row04_traceSegment_024_0324_0013, g32p_row04_traceSegment_024_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 364 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 351 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 351 13 14, g32p_row04_traceSegment_024_0351_0013, g32p_row04_traceSegment_024_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 324 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 324 27 27, g32p_row04_traceSegment_024_0324_0027, g32p_row04_traceSegment_024_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 378 13 14, g32p_row04_traceSegment_024_0378_0013, g32p_row04_traceSegment_024_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 405 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 405 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 405 13 14, g32p_row04_traceSegment_024_0405_0013, g32p_row04_traceSegment_024_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 378 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 378 27 27, g32p_row04_traceSegment_024_0378_0027, g32p_row04_traceSegment_024_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 324 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 324 54 54, g32p_row04_traceSegment_024_0324_0054, g32p_row04_traceSegment_024_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_024 216 216 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 216 108 108, g32p_row04_traceSegment_024_0216_0108, g32p_row04_traceSegment_024_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_024 0 432 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 0 216 216, g32p_row04_traceSegment_024_0000_0216, g32p_row04_traceSegment_024_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 445 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 432 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 432 13 14, g32p_row04_traceSegment_024_0432_0013, g32p_row04_traceSegment_024_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 472 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 459 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 459 13 14, g32p_row04_traceSegment_024_0459_0013, g32p_row04_traceSegment_024_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 432 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 432 27 27, g32p_row04_traceSegment_024_0432_0027, g32p_row04_traceSegment_024_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 486 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 499 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 486 27 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 486 13 14, g32p_row04_traceSegment_024_0486_0013, g32p_row04_traceSegment_024_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 513 13 14, g32p_row04_traceSegment_024_0513_0013, g32p_row04_traceSegment_024_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 486 54 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 486 27 27, g32p_row04_traceSegment_024_0486_0027, g32p_row04_traceSegment_024_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 432 108 = [0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 432 54 54, g32p_row04_traceSegment_024_0432_0054, g32p_row04_traceSegment_024_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 553 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 540 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 540 13 14, g32p_row04_traceSegment_024_0540_0013, g32p_row04_traceSegment_024_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 567 13 14, g32p_row04_traceSegment_024_0567_0013, g32p_row04_traceSegment_024_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 540 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 540 27 27, g32p_row04_traceSegment_024_0540_0027, g32p_row04_traceSegment_024_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 607 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 594 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 594 13 14, g32p_row04_traceSegment_024_0594_0013, g32p_row04_traceSegment_024_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 621 13 14, g32p_row04_traceSegment_024_0621_0013, g32p_row04_traceSegment_024_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 594 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 594 27 27, g32p_row04_traceSegment_024_0594_0027, g32p_row04_traceSegment_024_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 540 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 540 54 54, g32p_row04_traceSegment_024_0540_0054, g32p_row04_traceSegment_024_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_024 432 216 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 432 108 108, g32p_row04_traceSegment_024_0432_0108, g32p_row04_traceSegment_024_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 648 13 14, g32p_row04_traceSegment_024_0648_0013, g32p_row04_traceSegment_024_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 675 13 14, g32p_row04_traceSegment_024_0675_0013, g32p_row04_traceSegment_024_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 648 27 27, g32p_row04_traceSegment_024_0648_0027, g32p_row04_traceSegment_024_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 702 13 14, g32p_row04_traceSegment_024_0702_0013, g32p_row04_traceSegment_024_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 729 13 14, g32p_row04_traceSegment_024_0729_0013, g32p_row04_traceSegment_024_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 702 27 27, g32p_row04_traceSegment_024_0702_0027, g32p_row04_traceSegment_024_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 648 54 54, g32p_row04_traceSegment_024_0648_0054, g32p_row04_traceSegment_024_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 756 13 14, g32p_row04_traceSegment_024_0756_0013, g32p_row04_traceSegment_024_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 783 13 14, g32p_row04_traceSegment_024_0783_0013, g32p_row04_traceSegment_024_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 756 27 27, g32p_row04_traceSegment_024_0756_0027, g32p_row04_traceSegment_024_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 810 13 14, g32p_row04_traceSegment_024_0810_0013, g32p_row04_traceSegment_024_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 837 13 14, g32p_row04_traceSegment_024_0837_0013, g32p_row04_traceSegment_024_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 810 27 27, g32p_row04_traceSegment_024_0810_0027, g32p_row04_traceSegment_024_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 756 54 54, g32p_row04_traceSegment_024_0756_0054, g32p_row04_traceSegment_024_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_024 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 648 108 108, g32p_row04_traceSegment_024_0648_0108, g32p_row04_traceSegment_024_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_024 432 432 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 432 216 216, g32p_row04_traceSegment_024_0432_0216, g32p_row04_traceSegment_024_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_024 0 864 = [0, 12, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 0 432 432, g32p_row04_traceSegment_024_0000_0432, g32p_row04_traceSegment_024_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 864 13 14, g32p_row04_traceSegment_024_0864_0013, g32p_row04_traceSegment_024_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 891 13 14, g32p_row04_traceSegment_024_0891_0013, g32p_row04_traceSegment_024_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 864 27 27, g32p_row04_traceSegment_024_0864_0027, g32p_row04_traceSegment_024_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 918 13 14, g32p_row04_traceSegment_024_0918_0013, g32p_row04_traceSegment_024_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 945 13 14, g32p_row04_traceSegment_024_0945_0013, g32p_row04_traceSegment_024_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 918 27 27, g32p_row04_traceSegment_024_0918_0027, g32p_row04_traceSegment_024_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 864 54 54, g32p_row04_traceSegment_024_0864_0054, g32p_row04_traceSegment_024_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 972 13 14, g32p_row04_traceSegment_024_0972_0013, g32p_row04_traceSegment_024_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 999 13 14, g32p_row04_traceSegment_024_0999_0013, g32p_row04_traceSegment_024_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 972 27 27, g32p_row04_traceSegment_024_0972_0027, g32p_row04_traceSegment_024_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1026 13 14, g32p_row04_traceSegment_024_1026_0013, g32p_row04_traceSegment_024_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1053 13 14, g32p_row04_traceSegment_024_1053_0013, g32p_row04_traceSegment_024_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1026 27 27, g32p_row04_traceSegment_024_1026_0027, g32p_row04_traceSegment_024_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 972 54 54, g32p_row04_traceSegment_024_0972_0054, g32p_row04_traceSegment_024_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_024 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 864 108 108, g32p_row04_traceSegment_024_0864_0108, g32p_row04_traceSegment_024_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1080 13 14, g32p_row04_traceSegment_024_1080_0013, g32p_row04_traceSegment_024_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1107 13 14, g32p_row04_traceSegment_024_1107_0013, g32p_row04_traceSegment_024_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1080 27 27, g32p_row04_traceSegment_024_1080_0027, g32p_row04_traceSegment_024_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1134 13 14, g32p_row04_traceSegment_024_1134_0013, g32p_row04_traceSegment_024_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1161 13 14, g32p_row04_traceSegment_024_1161_0013, g32p_row04_traceSegment_024_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1134 27 27, g32p_row04_traceSegment_024_1134_0027, g32p_row04_traceSegment_024_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1080 54 54, g32p_row04_traceSegment_024_1080_0054, g32p_row04_traceSegment_024_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1188 13 14, g32p_row04_traceSegment_024_1188_0013, g32p_row04_traceSegment_024_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1215 13 14, g32p_row04_traceSegment_024_1215_0013, g32p_row04_traceSegment_024_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1188 27 27, g32p_row04_traceSegment_024_1188_0027, g32p_row04_traceSegment_024_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1242 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1255 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1242 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1242 13 14, g32p_row04_traceSegment_024_1242_0013, g32p_row04_traceSegment_024_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1269 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1269 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1269 13 14, g32p_row04_traceSegment_024_1269_0013, g32p_row04_traceSegment_024_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1242 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1242 27 27, g32p_row04_traceSegment_024_1242_0027, g32p_row04_traceSegment_024_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 1188 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1188 54 54, g32p_row04_traceSegment_024_1188_0054, g32p_row04_traceSegment_024_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_024 1080 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1080 108 108, g32p_row04_traceSegment_024_1080_0108, g32p_row04_traceSegment_024_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_024 864 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 864 216 216, g32p_row04_traceSegment_024_0864_0216, g32p_row04_traceSegment_024_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1296 13 14, g32p_row04_traceSegment_024_1296_0013, g32p_row04_traceSegment_024_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1323 13 14, g32p_row04_traceSegment_024_1323_0013, g32p_row04_traceSegment_024_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1296 27 27, g32p_row04_traceSegment_024_1296_0027, g32p_row04_traceSegment_024_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1350 13 14, g32p_row04_traceSegment_024_1350_0013, g32p_row04_traceSegment_024_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1377 13 14, g32p_row04_traceSegment_024_1377_0013, g32p_row04_traceSegment_024_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1350 27 27, g32p_row04_traceSegment_024_1350_0027, g32p_row04_traceSegment_024_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1296 54 54, g32p_row04_traceSegment_024_1296_0054, g32p_row04_traceSegment_024_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1404 13 14, g32p_row04_traceSegment_024_1404_0013, g32p_row04_traceSegment_024_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1431 13 14, g32p_row04_traceSegment_024_1431_0013, g32p_row04_traceSegment_024_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1404 27 27, g32p_row04_traceSegment_024_1404_0027, g32p_row04_traceSegment_024_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1458 13 14, g32p_row04_traceSegment_024_1458_0013, g32p_row04_traceSegment_024_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1485 13 14, g32p_row04_traceSegment_024_1485_0013, g32p_row04_traceSegment_024_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1458 27 27, g32p_row04_traceSegment_024_1458_0027, g32p_row04_traceSegment_024_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1404 54 54, g32p_row04_traceSegment_024_1404_0054, g32p_row04_traceSegment_024_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_024 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1296 108 108, g32p_row04_traceSegment_024_1296_0108, g32p_row04_traceSegment_024_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1512 13 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1525 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1512 27 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1512 13 14, g32p_row04_traceSegment_024_1512_0013, g32p_row04_traceSegment_024_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1539 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1539 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1539 13 14, g32p_row04_traceSegment_024_1539_0013, g32p_row04_traceSegment_024_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1512 54 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1512 27 27, g32p_row04_traceSegment_024_1512_0027, g32p_row04_traceSegment_024_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1566 13 14, g32p_row04_traceSegment_024_1566_0013, g32p_row04_traceSegment_024_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1593 13 14, g32p_row04_traceSegment_024_1593_0013, g32p_row04_traceSegment_024_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1566 27 27, g32p_row04_traceSegment_024_1566_0027, g32p_row04_traceSegment_024_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 1512 108 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1512 54 54, g32p_row04_traceSegment_024_1512_0054, g32p_row04_traceSegment_024_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1633 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1620 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1620 13 14, g32p_row04_traceSegment_024_1620_0013, g32p_row04_traceSegment_024_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1660 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1647 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1647 13 14, g32p_row04_traceSegment_024_1647_0013, g32p_row04_traceSegment_024_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1620 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1620 27 27, g32p_row04_traceSegment_024_1620_0027, g32p_row04_traceSegment_024_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1674 13 14, g32p_row04_traceSegment_024_1674_0013, g32p_row04_traceSegment_024_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_024 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_024 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_024_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_024 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1701 13 14, g32p_row04_traceSegment_024_1701_0013, g32p_row04_traceSegment_024_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_024 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1674 27 27, g32p_row04_traceSegment_024_1674_0027, g32p_row04_traceSegment_024_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_024 1620 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1620 54 54, g32p_row04_traceSegment_024_1620_0054, g32p_row04_traceSegment_024_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_024 1512 216 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1512 108 108, g32p_row04_traceSegment_024_1512_0108, g32p_row04_traceSegment_024_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_024_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_024 1296 432 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 1296 216 216, g32p_row04_traceSegment_024_1296_0216, g32p_row04_traceSegment_024_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_024 864 864 = [0, 4, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 864 432 432, g32p_row04_traceSegment_024_0864_0432, g32p_row04_traceSegment_024_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_024_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_024 0 1728 = [0, 16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_024 0 864 864, g32p_row04_traceSegment_024_0000_0864, g32p_row04_traceSegment_024_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 24 = [0, 16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_024_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_025 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 25 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_025_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 0 13 14, g32p_row04_traceSegment_025_0000_0013, g32p_row04_traceSegment_025_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 27 13 14, g32p_row04_traceSegment_025_0027_0013, g32p_row04_traceSegment_025_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 0 27 27, g32p_row04_traceSegment_025_0000_0027, g32p_row04_traceSegment_025_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 54 13 14, g32p_row04_traceSegment_025_0054_0013, g32p_row04_traceSegment_025_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 81 13 14, g32p_row04_traceSegment_025_0081_0013, g32p_row04_traceSegment_025_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 54 27 27, g32p_row04_traceSegment_025_0054_0027, g32p_row04_traceSegment_025_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 0 54 54, g32p_row04_traceSegment_025_0000_0054, g32p_row04_traceSegment_025_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 108 13 14, g32p_row04_traceSegment_025_0108_0013, g32p_row04_traceSegment_025_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 135 13 14, g32p_row04_traceSegment_025_0135_0013, g32p_row04_traceSegment_025_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 108 27 27, g32p_row04_traceSegment_025_0108_0027, g32p_row04_traceSegment_025_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 162 13 14, g32p_row04_traceSegment_025_0162_0013, g32p_row04_traceSegment_025_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 189 13 14, g32p_row04_traceSegment_025_0189_0013, g32p_row04_traceSegment_025_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 162 27 27, g32p_row04_traceSegment_025_0162_0027, g32p_row04_traceSegment_025_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 108 54 54, g32p_row04_traceSegment_025_0108_0054, g32p_row04_traceSegment_025_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_025 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 0 108 108, g32p_row04_traceSegment_025_0000_0108, g32p_row04_traceSegment_025_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 216 13 14, g32p_row04_traceSegment_025_0216_0013, g32p_row04_traceSegment_025_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 243 13 14, g32p_row04_traceSegment_025_0243_0013, g32p_row04_traceSegment_025_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 216 27 27, g32p_row04_traceSegment_025_0216_0027, g32p_row04_traceSegment_025_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 270 13 14, g32p_row04_traceSegment_025_0270_0013, g32p_row04_traceSegment_025_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 297 13 14, g32p_row04_traceSegment_025_0297_0013, g32p_row04_traceSegment_025_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 270 27 27, g32p_row04_traceSegment_025_0270_0027, g32p_row04_traceSegment_025_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 216 54 54, g32p_row04_traceSegment_025_0216_0054, g32p_row04_traceSegment_025_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 324 13 14, g32p_row04_traceSegment_025_0324_0013, g32p_row04_traceSegment_025_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 364 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 351 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 351 13 14, g32p_row04_traceSegment_025_0351_0013, g32p_row04_traceSegment_025_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 324 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 324 27 27, g32p_row04_traceSegment_025_0324_0027, g32p_row04_traceSegment_025_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 378 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 378 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 378 13 14, g32p_row04_traceSegment_025_0378_0013, g32p_row04_traceSegment_025_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 405 13 14, g32p_row04_traceSegment_025_0405_0013, g32p_row04_traceSegment_025_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 378 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 378 27 27, g32p_row04_traceSegment_025_0378_0027, g32p_row04_traceSegment_025_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 324 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 324 54 54, g32p_row04_traceSegment_025_0324_0054, g32p_row04_traceSegment_025_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_025 216 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 216 108 108, g32p_row04_traceSegment_025_0216_0108, g32p_row04_traceSegment_025_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_025 0 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 0 216 216, g32p_row04_traceSegment_025_0000_0216, g32p_row04_traceSegment_025_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 432 13 14, g32p_row04_traceSegment_025_0432_0013, g32p_row04_traceSegment_025_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 472 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 459 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 459 13 14, g32p_row04_traceSegment_025_0459_0013, g32p_row04_traceSegment_025_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 432 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 432 27 27, g32p_row04_traceSegment_025_0432_0027, g32p_row04_traceSegment_025_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 486 13 14, g32p_row04_traceSegment_025_0486_0013, g32p_row04_traceSegment_025_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 513 13 14, g32p_row04_traceSegment_025_0513_0013, g32p_row04_traceSegment_025_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 486 27 27, g32p_row04_traceSegment_025_0486_0027, g32p_row04_traceSegment_025_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 432 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 432 54 54, g32p_row04_traceSegment_025_0432_0054, g32p_row04_traceSegment_025_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 540 13 14, g32p_row04_traceSegment_025_0540_0013, g32p_row04_traceSegment_025_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 567 13 14, g32p_row04_traceSegment_025_0567_0013, g32p_row04_traceSegment_025_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 540 27 27, g32p_row04_traceSegment_025_0540_0027, g32p_row04_traceSegment_025_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 594 13 14, g32p_row04_traceSegment_025_0594_0013, g32p_row04_traceSegment_025_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 621 13 14, g32p_row04_traceSegment_025_0621_0013, g32p_row04_traceSegment_025_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 594 27 27, g32p_row04_traceSegment_025_0594_0027, g32p_row04_traceSegment_025_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 540 54 54, g32p_row04_traceSegment_025_0540_0054, g32p_row04_traceSegment_025_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_025 432 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 432 108 108, g32p_row04_traceSegment_025_0432_0108, g32p_row04_traceSegment_025_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 648 13 14, g32p_row04_traceSegment_025_0648_0013, g32p_row04_traceSegment_025_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 675 13 14, g32p_row04_traceSegment_025_0675_0013, g32p_row04_traceSegment_025_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 648 27 27, g32p_row04_traceSegment_025_0648_0027, g32p_row04_traceSegment_025_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 702 13 14, g32p_row04_traceSegment_025_0702_0013, g32p_row04_traceSegment_025_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 729 13 14, g32p_row04_traceSegment_025_0729_0013, g32p_row04_traceSegment_025_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 702 27 27, g32p_row04_traceSegment_025_0702_0027, g32p_row04_traceSegment_025_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 648 54 54, g32p_row04_traceSegment_025_0648_0054, g32p_row04_traceSegment_025_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 756 13 14, g32p_row04_traceSegment_025_0756_0013, g32p_row04_traceSegment_025_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 783 13 14, g32p_row04_traceSegment_025_0783_0013, g32p_row04_traceSegment_025_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 756 27 27, g32p_row04_traceSegment_025_0756_0027, g32p_row04_traceSegment_025_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 810 13 14, g32p_row04_traceSegment_025_0810_0013, g32p_row04_traceSegment_025_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 837 13 14, g32p_row04_traceSegment_025_0837_0013, g32p_row04_traceSegment_025_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 810 27 27, g32p_row04_traceSegment_025_0810_0027, g32p_row04_traceSegment_025_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 756 54 54, g32p_row04_traceSegment_025_0756_0054, g32p_row04_traceSegment_025_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_025 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 648 108 108, g32p_row04_traceSegment_025_0648_0108, g32p_row04_traceSegment_025_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_025 432 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 432 216 216, g32p_row04_traceSegment_025_0432_0216, g32p_row04_traceSegment_025_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_025 0 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 0 432 432, g32p_row04_traceSegment_025_0000_0432, g32p_row04_traceSegment_025_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 864 13 14, g32p_row04_traceSegment_025_0864_0013, g32p_row04_traceSegment_025_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 891 13 14, g32p_row04_traceSegment_025_0891_0013, g32p_row04_traceSegment_025_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 864 27 27, g32p_row04_traceSegment_025_0864_0027, g32p_row04_traceSegment_025_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 918 13 14, g32p_row04_traceSegment_025_0918_0013, g32p_row04_traceSegment_025_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 945 13 14, g32p_row04_traceSegment_025_0945_0013, g32p_row04_traceSegment_025_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 918 27 27, g32p_row04_traceSegment_025_0918_0027, g32p_row04_traceSegment_025_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 864 54 54, g32p_row04_traceSegment_025_0864_0054, g32p_row04_traceSegment_025_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 972 13 14, g32p_row04_traceSegment_025_0972_0013, g32p_row04_traceSegment_025_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 999 13 14, g32p_row04_traceSegment_025_0999_0013, g32p_row04_traceSegment_025_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 972 27 27, g32p_row04_traceSegment_025_0972_0027, g32p_row04_traceSegment_025_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1026 13 14, g32p_row04_traceSegment_025_1026_0013, g32p_row04_traceSegment_025_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1053 13 14, g32p_row04_traceSegment_025_1053_0013, g32p_row04_traceSegment_025_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1026 27 27, g32p_row04_traceSegment_025_1026_0027, g32p_row04_traceSegment_025_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 972 54 54, g32p_row04_traceSegment_025_0972_0054, g32p_row04_traceSegment_025_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_025 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 864 108 108, g32p_row04_traceSegment_025_0864_0108, g32p_row04_traceSegment_025_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1080 13 14, g32p_row04_traceSegment_025_1080_0013, g32p_row04_traceSegment_025_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1107 13 14, g32p_row04_traceSegment_025_1107_0013, g32p_row04_traceSegment_025_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1080 27 27, g32p_row04_traceSegment_025_1080_0027, g32p_row04_traceSegment_025_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1134 13 14, g32p_row04_traceSegment_025_1134_0013, g32p_row04_traceSegment_025_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1161 13 14, g32p_row04_traceSegment_025_1161_0013, g32p_row04_traceSegment_025_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1134 27 27, g32p_row04_traceSegment_025_1134_0027, g32p_row04_traceSegment_025_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1080 54 54, g32p_row04_traceSegment_025_1080_0054, g32p_row04_traceSegment_025_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1188 13 14, g32p_row04_traceSegment_025_1188_0013, g32p_row04_traceSegment_025_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1228 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1215 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1215 13 14, g32p_row04_traceSegment_025_1215_0013, g32p_row04_traceSegment_025_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1188 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1188 27 27, g32p_row04_traceSegment_025_1188_0027, g32p_row04_traceSegment_025_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1242 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1255 14 = [6] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1242 27 = [9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1242 13 14, g32p_row04_traceSegment_025_1242_0013, g32p_row04_traceSegment_025_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1269 13 = [4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1282 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1269 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1269 13 14, g32p_row04_traceSegment_025_1269_0013, g32p_row04_traceSegment_025_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1242 54 = [14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1242 27 27, g32p_row04_traceSegment_025_1242_0027, g32p_row04_traceSegment_025_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 1188 108 = [17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1188 54 54, g32p_row04_traceSegment_025_1188_0054, g32p_row04_traceSegment_025_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_025 1080 216 = [17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1080 108 108, g32p_row04_traceSegment_025_1080_0108, g32p_row04_traceSegment_025_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_025 864 432 = [17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 864 216 216, g32p_row04_traceSegment_025_0864_0216, g32p_row04_traceSegment_025_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1309 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1296 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1296 13 14, g32p_row04_traceSegment_025_1296_0013, g32p_row04_traceSegment_025_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1323 13 14, g32p_row04_traceSegment_025_1323_0013, g32p_row04_traceSegment_025_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1296 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1296 27 27, g32p_row04_traceSegment_025_1296_0027, g32p_row04_traceSegment_025_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1350 13 14, g32p_row04_traceSegment_025_1350_0013, g32p_row04_traceSegment_025_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1377 13 14, g32p_row04_traceSegment_025_1377_0013, g32p_row04_traceSegment_025_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1350 27 27, g32p_row04_traceSegment_025_1350_0027, g32p_row04_traceSegment_025_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 1296 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1296 54 54, g32p_row04_traceSegment_025_1296_0054, g32p_row04_traceSegment_025_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1417 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1404 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1404 13 14, g32p_row04_traceSegment_025_1404_0013, g32p_row04_traceSegment_025_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1444 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1431 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1431 13 14, g32p_row04_traceSegment_025_1431_0013, g32p_row04_traceSegment_025_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1404 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1404 27 27, g32p_row04_traceSegment_025_1404_0027, g32p_row04_traceSegment_025_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1471 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1458 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1458 13 14, g32p_row04_traceSegment_025_1458_0013, g32p_row04_traceSegment_025_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1485 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1498 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1485 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1485 13 14, g32p_row04_traceSegment_025_1485_0013, g32p_row04_traceSegment_025_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1458 54 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1458 27 27, g32p_row04_traceSegment_025_1458_0027, g32p_row04_traceSegment_025_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 1404 108 = [8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1404 54 54, g32p_row04_traceSegment_025_1404_0054, g32p_row04_traceSegment_025_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_025 1296 216 = [11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1296 108 108, g32p_row04_traceSegment_025_1296_0108, g32p_row04_traceSegment_025_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1512 13 14, g32p_row04_traceSegment_025_1512_0013, g32p_row04_traceSegment_025_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1539 13 14, g32p_row04_traceSegment_025_1539_0013, g32p_row04_traceSegment_025_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1512 27 27, g32p_row04_traceSegment_025_1512_0027, g32p_row04_traceSegment_025_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1566 13 14, g32p_row04_traceSegment_025_1566_0013, g32p_row04_traceSegment_025_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1593 13 14, g32p_row04_traceSegment_025_1593_0013, g32p_row04_traceSegment_025_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1566 27 27, g32p_row04_traceSegment_025_1566_0027, g32p_row04_traceSegment_025_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1512 54 54, g32p_row04_traceSegment_025_1512_0054, g32p_row04_traceSegment_025_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1620 13 14, g32p_row04_traceSegment_025_1620_0013, g32p_row04_traceSegment_025_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1647 13 14, g32p_row04_traceSegment_025_1647_0013, g32p_row04_traceSegment_025_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1620 27 27, g32p_row04_traceSegment_025_1620_0027, g32p_row04_traceSegment_025_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1674 13 14, g32p_row04_traceSegment_025_1674_0013, g32p_row04_traceSegment_025_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_025 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_025 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_025_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_025 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1701 13 14, g32p_row04_traceSegment_025_1701_0013, g32p_row04_traceSegment_025_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_025 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1674 27 27, g32p_row04_traceSegment_025_1674_0027, g32p_row04_traceSegment_025_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_025 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1620 54 54, g32p_row04_traceSegment_025_1620_0054, g32p_row04_traceSegment_025_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_025 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1512 108 108, g32p_row04_traceSegment_025_1512_0108, g32p_row04_traceSegment_025_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_025_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_025 1296 432 = [11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 1296 216 216, g32p_row04_traceSegment_025_1296_0216, g32p_row04_traceSegment_025_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_025 864 864 = [28] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 864 432 432, g32p_row04_traceSegment_025_0864_0432, g32p_row04_traceSegment_025_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_025_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_025 0 1728 = [32] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_025 0 864 864, g32p_row04_traceSegment_025_0000_0864, g32p_row04_traceSegment_025_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 25 = [32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_025_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_027 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 27 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_027_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 0 13 14, g32p_row04_traceSegment_027_0000_0013, g32p_row04_traceSegment_027_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 40 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 27 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 27 13 14, g32p_row04_traceSegment_027_0027_0013, g32p_row04_traceSegment_027_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 0 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 0 27 27, g32p_row04_traceSegment_027_0000_0027, g32p_row04_traceSegment_027_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 54 13 = [0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 54 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 54 13 14, g32p_row04_traceSegment_027_0054_0013, g32p_row04_traceSegment_027_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 81 13 14, g32p_row04_traceSegment_027_0081_0013, g32p_row04_traceSegment_027_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 54 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 54 27 27, g32p_row04_traceSegment_027_0054_0027, g32p_row04_traceSegment_027_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 0 108 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 0 54 54, g32p_row04_traceSegment_027_0000_0054, g32p_row04_traceSegment_027_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 108 13 14, g32p_row04_traceSegment_027_0108_0013, g32p_row04_traceSegment_027_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 135 13 14, g32p_row04_traceSegment_027_0135_0013, g32p_row04_traceSegment_027_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 108 27 27, g32p_row04_traceSegment_027_0108_0027, g32p_row04_traceSegment_027_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 162 13 14, g32p_row04_traceSegment_027_0162_0013, g32p_row04_traceSegment_027_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 189 13 14, g32p_row04_traceSegment_027_0189_0013, g32p_row04_traceSegment_027_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 162 27 27, g32p_row04_traceSegment_027_0162_0027, g32p_row04_traceSegment_027_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 108 54 54, g32p_row04_traceSegment_027_0108_0054, g32p_row04_traceSegment_027_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_027 0 216 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 0 108 108, g32p_row04_traceSegment_027_0000_0108, g32p_row04_traceSegment_027_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 216 13 14, g32p_row04_traceSegment_027_0216_0013, g32p_row04_traceSegment_027_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 243 13 14, g32p_row04_traceSegment_027_0243_0013, g32p_row04_traceSegment_027_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 216 27 27, g32p_row04_traceSegment_027_0216_0027, g32p_row04_traceSegment_027_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 270 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 283 14 = [0, 1, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 270 27 = [0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 270 13 14, g32p_row04_traceSegment_027_0270_0013, g32p_row04_traceSegment_027_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 297 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 310 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 297 27 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 297 13 14, g32p_row04_traceSegment_027_0297_0013, g32p_row04_traceSegment_027_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 270 54 = [0, 3, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 270 27 27, g32p_row04_traceSegment_027_0270_0027, g32p_row04_traceSegment_027_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 216 108 = [0, 3, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 216 54 54, g32p_row04_traceSegment_027_0216_0054, g32p_row04_traceSegment_027_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 324 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 324 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 324 13 14, g32p_row04_traceSegment_027_0324_0013, g32p_row04_traceSegment_027_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 364 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 351 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 351 13 14, g32p_row04_traceSegment_027_0351_0013, g32p_row04_traceSegment_027_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 324 54 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 324 27 27, g32p_row04_traceSegment_027_0324_0027, g32p_row04_traceSegment_027_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 378 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 391 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 378 27 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 378 13 14, g32p_row04_traceSegment_027_0378_0013, g32p_row04_traceSegment_027_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 405 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 418 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 405 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 405 13 14, g32p_row04_traceSegment_027_0405_0013, g32p_row04_traceSegment_027_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 378 54 = [0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 378 27 27, g32p_row04_traceSegment_027_0378_0027, g32p_row04_traceSegment_027_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 324 108 = [0, 3, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 324 54 54, g32p_row04_traceSegment_027_0324_0054, g32p_row04_traceSegment_027_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_027 216 216 = [0, 6, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 216 108 108, g32p_row04_traceSegment_027_0216_0108, g32p_row04_traceSegment_027_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_027 0 432 = [0, 12, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 0 216 216, g32p_row04_traceSegment_027_0000_0216, g32p_row04_traceSegment_027_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 445 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 432 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 432 13 14, g32p_row04_traceSegment_027_0432_0013, g32p_row04_traceSegment_027_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 459 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 472 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 459 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 459 13 14, g32p_row04_traceSegment_027_0459_0013, g32p_row04_traceSegment_027_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 432 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 432 27 27, g32p_row04_traceSegment_027_0432_0027, g32p_row04_traceSegment_027_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 486 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 499 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 486 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 486 13 14, g32p_row04_traceSegment_027_0486_0013, g32p_row04_traceSegment_027_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 513 13 14, g32p_row04_traceSegment_027_0513_0013, g32p_row04_traceSegment_027_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 486 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 486 27 27, g32p_row04_traceSegment_027_0486_0027, g32p_row04_traceSegment_027_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 432 108 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 432 54 54, g32p_row04_traceSegment_027_0432_0054, g32p_row04_traceSegment_027_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 540 13 14, g32p_row04_traceSegment_027_0540_0013, g32p_row04_traceSegment_027_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 567 13 14, g32p_row04_traceSegment_027_0567_0013, g32p_row04_traceSegment_027_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 540 27 27, g32p_row04_traceSegment_027_0540_0027, g32p_row04_traceSegment_027_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 594 13 14, g32p_row04_traceSegment_027_0594_0013, g32p_row04_traceSegment_027_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 621 13 14, g32p_row04_traceSegment_027_0621_0013, g32p_row04_traceSegment_027_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 594 27 27, g32p_row04_traceSegment_027_0594_0027, g32p_row04_traceSegment_027_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 540 54 54, g32p_row04_traceSegment_027_0540_0054, g32p_row04_traceSegment_027_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_027 432 216 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 432 108 108, g32p_row04_traceSegment_027_0432_0108, g32p_row04_traceSegment_027_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 648 13 14, g32p_row04_traceSegment_027_0648_0013, g32p_row04_traceSegment_027_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 675 13 14, g32p_row04_traceSegment_027_0675_0013, g32p_row04_traceSegment_027_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 648 27 27, g32p_row04_traceSegment_027_0648_0027, g32p_row04_traceSegment_027_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 702 13 14, g32p_row04_traceSegment_027_0702_0013, g32p_row04_traceSegment_027_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 729 13 14, g32p_row04_traceSegment_027_0729_0013, g32p_row04_traceSegment_027_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 702 27 27, g32p_row04_traceSegment_027_0702_0027, g32p_row04_traceSegment_027_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 648 54 54, g32p_row04_traceSegment_027_0648_0054, g32p_row04_traceSegment_027_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 756 13 14, g32p_row04_traceSegment_027_0756_0013, g32p_row04_traceSegment_027_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 783 13 14, g32p_row04_traceSegment_027_0783_0013, g32p_row04_traceSegment_027_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 756 27 27, g32p_row04_traceSegment_027_0756_0027, g32p_row04_traceSegment_027_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 810 13 14, g32p_row04_traceSegment_027_0810_0013, g32p_row04_traceSegment_027_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 837 13 14, g32p_row04_traceSegment_027_0837_0013, g32p_row04_traceSegment_027_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 810 27 27, g32p_row04_traceSegment_027_0810_0027, g32p_row04_traceSegment_027_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 756 54 54, g32p_row04_traceSegment_027_0756_0054, g32p_row04_traceSegment_027_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_027 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 648 108 108, g32p_row04_traceSegment_027_0648_0108, g32p_row04_traceSegment_027_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_027 432 432 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 432 216 216, g32p_row04_traceSegment_027_0432_0216, g32p_row04_traceSegment_027_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_027 0 864 = [0, 12, 18] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 0 432 432, g32p_row04_traceSegment_027_0000_0432, g32p_row04_traceSegment_027_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 864 13 14, g32p_row04_traceSegment_027_0864_0013, g32p_row04_traceSegment_027_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 891 13 14, g32p_row04_traceSegment_027_0891_0013, g32p_row04_traceSegment_027_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 864 27 27, g32p_row04_traceSegment_027_0864_0027, g32p_row04_traceSegment_027_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 918 13 14, g32p_row04_traceSegment_027_0918_0013, g32p_row04_traceSegment_027_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 945 13 14, g32p_row04_traceSegment_027_0945_0013, g32p_row04_traceSegment_027_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 918 27 27, g32p_row04_traceSegment_027_0918_0027, g32p_row04_traceSegment_027_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 864 54 54, g32p_row04_traceSegment_027_0864_0054, g32p_row04_traceSegment_027_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 972 13 14, g32p_row04_traceSegment_027_0972_0013, g32p_row04_traceSegment_027_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 999 13 14, g32p_row04_traceSegment_027_0999_0013, g32p_row04_traceSegment_027_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 972 27 27, g32p_row04_traceSegment_027_0972_0027, g32p_row04_traceSegment_027_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1026 13 14, g32p_row04_traceSegment_027_1026_0013, g32p_row04_traceSegment_027_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1053 13 14, g32p_row04_traceSegment_027_1053_0013, g32p_row04_traceSegment_027_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1026 27 27, g32p_row04_traceSegment_027_1026_0027, g32p_row04_traceSegment_027_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 972 54 54, g32p_row04_traceSegment_027_0972_0054, g32p_row04_traceSegment_027_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_027 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 864 108 108, g32p_row04_traceSegment_027_0864_0108, g32p_row04_traceSegment_027_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1080 13 14, g32p_row04_traceSegment_027_1080_0013, g32p_row04_traceSegment_027_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1107 13 14, g32p_row04_traceSegment_027_1107_0013, g32p_row04_traceSegment_027_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1080 27 27, g32p_row04_traceSegment_027_1080_0027, g32p_row04_traceSegment_027_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1134 13 14, g32p_row04_traceSegment_027_1134_0013, g32p_row04_traceSegment_027_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1161 13 14, g32p_row04_traceSegment_027_1161_0013, g32p_row04_traceSegment_027_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1134 27 27, g32p_row04_traceSegment_027_1134_0027, g32p_row04_traceSegment_027_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1080 54 54, g32p_row04_traceSegment_027_1080_0054, g32p_row04_traceSegment_027_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1188 13 14, g32p_row04_traceSegment_027_1188_0013, g32p_row04_traceSegment_027_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1215 13 14, g32p_row04_traceSegment_027_1215_0013, g32p_row04_traceSegment_027_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1188 27 27, g32p_row04_traceSegment_027_1188_0027, g32p_row04_traceSegment_027_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1255 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1242 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1242 13 14, g32p_row04_traceSegment_027_1242_0013, g32p_row04_traceSegment_027_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1269 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1269 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1269 13 14, g32p_row04_traceSegment_027_1269_0013, g32p_row04_traceSegment_027_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1242 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1242 27 27, g32p_row04_traceSegment_027_1242_0027, g32p_row04_traceSegment_027_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 1188 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1188 54 54, g32p_row04_traceSegment_027_1188_0054, g32p_row04_traceSegment_027_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_027 1080 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1080 108 108, g32p_row04_traceSegment_027_1080_0108, g32p_row04_traceSegment_027_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_027 864 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 864 216 216, g32p_row04_traceSegment_027_0864_0216, g32p_row04_traceSegment_027_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1309 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1296 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1296 13 14, g32p_row04_traceSegment_027_1296_0013, g32p_row04_traceSegment_027_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1323 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1323 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1323 13 14, g32p_row04_traceSegment_027_1323_0013, g32p_row04_traceSegment_027_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1296 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1296 27 27, g32p_row04_traceSegment_027_1296_0027, g32p_row04_traceSegment_027_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1350 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1350 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1350 13 14, g32p_row04_traceSegment_027_1350_0013, g32p_row04_traceSegment_027_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1377 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1390 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1377 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1377 13 14, g32p_row04_traceSegment_027_1377_0013, g32p_row04_traceSegment_027_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1350 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1350 27 27, g32p_row04_traceSegment_027_1350_0027, g32p_row04_traceSegment_027_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 1296 108 = [0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1296 54 54, g32p_row04_traceSegment_027_1296_0054, g32p_row04_traceSegment_027_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1404 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1417 14 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1404 27 = [0, 4, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1404 13 14, g32p_row04_traceSegment_027_1404_0013, g32p_row04_traceSegment_027_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1431 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1431 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1431 13 14, g32p_row04_traceSegment_027_1431_0013, g32p_row04_traceSegment_027_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1404 54 = [0, 7, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1404 27 27, g32p_row04_traceSegment_027_1404_0027, g32p_row04_traceSegment_027_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1458 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1458 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1458 13 14, g32p_row04_traceSegment_027_1458_0013, g32p_row04_traceSegment_027_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1498 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1485 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1485 13 14, g32p_row04_traceSegment_027_1485_0013, g32p_row04_traceSegment_027_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1458 54 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1458 27 27, g32p_row04_traceSegment_027_1458_0027, g32p_row04_traceSegment_027_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 1404 108 = [0, 8, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1404 54 54, g32p_row04_traceSegment_027_1404_0054, g32p_row04_traceSegment_027_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_027 1296 216 = [0, 12, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1296 108 108, g32p_row04_traceSegment_027_1296_0108, g32p_row04_traceSegment_027_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1512 13 14, g32p_row04_traceSegment_027_1512_0013, g32p_row04_traceSegment_027_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1539 13 14, g32p_row04_traceSegment_027_1539_0013, g32p_row04_traceSegment_027_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1512 27 27, g32p_row04_traceSegment_027_1512_0027, g32p_row04_traceSegment_027_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1566 13 14, g32p_row04_traceSegment_027_1566_0013, g32p_row04_traceSegment_027_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1593 13 14, g32p_row04_traceSegment_027_1593_0013, g32p_row04_traceSegment_027_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1566 27 27, g32p_row04_traceSegment_027_1566_0027, g32p_row04_traceSegment_027_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1512 54 54, g32p_row04_traceSegment_027_1512_0054, g32p_row04_traceSegment_027_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1620 13 14, g32p_row04_traceSegment_027_1620_0013, g32p_row04_traceSegment_027_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1647 13 14, g32p_row04_traceSegment_027_1647_0013, g32p_row04_traceSegment_027_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1620 27 27, g32p_row04_traceSegment_027_1620_0027, g32p_row04_traceSegment_027_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1674 13 14, g32p_row04_traceSegment_027_1674_0013, g32p_row04_traceSegment_027_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_027 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_027 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_027_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_027 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1701 13 14, g32p_row04_traceSegment_027_1701_0013, g32p_row04_traceSegment_027_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_027 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1674 27 27, g32p_row04_traceSegment_027_1674_0027, g32p_row04_traceSegment_027_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_027 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1620 54 54, g32p_row04_traceSegment_027_1620_0054, g32p_row04_traceSegment_027_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_027 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1512 108 108, g32p_row04_traceSegment_027_1512_0108, g32p_row04_traceSegment_027_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_027_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_027 1296 432 = [0, 12, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 1296 216 216, g32p_row04_traceSegment_027_1296_0216, g32p_row04_traceSegment_027_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_027 864 864 = [0, 12, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 864 432 432, g32p_row04_traceSegment_027_0864_0432, g32p_row04_traceSegment_027_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_027_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_027 0 1728 = [0, 24, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_027 0 864 864, g32p_row04_traceSegment_027_0000_0864, g32p_row04_traceSegment_027_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_027 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 27 = [0, 24, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_027_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_028 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 28 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_028_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 0 13 14, g32p_row04_traceSegment_028_0000_0013, g32p_row04_traceSegment_028_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 27 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 40 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 27 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 27 13 14, g32p_row04_traceSegment_028_0027_0013, g32p_row04_traceSegment_028_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 0 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 0 27 27, g32p_row04_traceSegment_028_0000_0027, g32p_row04_traceSegment_028_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 54 13 14, g32p_row04_traceSegment_028_0054_0013, g32p_row04_traceSegment_028_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 81 13 14, g32p_row04_traceSegment_028_0081_0013, g32p_row04_traceSegment_028_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 54 27 27, g32p_row04_traceSegment_028_0054_0027, g32p_row04_traceSegment_028_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 0 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 0 54 54, g32p_row04_traceSegment_028_0000_0054, g32p_row04_traceSegment_028_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 108 13 14, g32p_row04_traceSegment_028_0108_0013, g32p_row04_traceSegment_028_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 135 13 14, g32p_row04_traceSegment_028_0135_0013, g32p_row04_traceSegment_028_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 108 27 27, g32p_row04_traceSegment_028_0108_0027, g32p_row04_traceSegment_028_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 162 13 14, g32p_row04_traceSegment_028_0162_0013, g32p_row04_traceSegment_028_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 189 13 14, g32p_row04_traceSegment_028_0189_0013, g32p_row04_traceSegment_028_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 162 27 27, g32p_row04_traceSegment_028_0162_0027, g32p_row04_traceSegment_028_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 108 54 54, g32p_row04_traceSegment_028_0108_0054, g32p_row04_traceSegment_028_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_028 0 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 0 108 108, g32p_row04_traceSegment_028_0000_0108, g32p_row04_traceSegment_028_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 216 13 14, g32p_row04_traceSegment_028_0216_0013, g32p_row04_traceSegment_028_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 243 13 14, g32p_row04_traceSegment_028_0243_0013, g32p_row04_traceSegment_028_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 216 27 27, g32p_row04_traceSegment_028_0216_0027, g32p_row04_traceSegment_028_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 270 13 14, g32p_row04_traceSegment_028_0270_0013, g32p_row04_traceSegment_028_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 297 13 14, g32p_row04_traceSegment_028_0297_0013, g32p_row04_traceSegment_028_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 270 27 27, g32p_row04_traceSegment_028_0270_0027, g32p_row04_traceSegment_028_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 216 54 54, g32p_row04_traceSegment_028_0216_0054, g32p_row04_traceSegment_028_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 324 13 14, g32p_row04_traceSegment_028_0324_0013, g32p_row04_traceSegment_028_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 351 13 14, g32p_row04_traceSegment_028_0351_0013, g32p_row04_traceSegment_028_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 324 27 27, g32p_row04_traceSegment_028_0324_0027, g32p_row04_traceSegment_028_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 378 13 14, g32p_row04_traceSegment_028_0378_0013, g32p_row04_traceSegment_028_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 405 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 418 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 405 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 405 13 14, g32p_row04_traceSegment_028_0405_0013, g32p_row04_traceSegment_028_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 378 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 378 27 27, g32p_row04_traceSegment_028_0378_0027, g32p_row04_traceSegment_028_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 324 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 324 54 54, g32p_row04_traceSegment_028_0324_0054, g32p_row04_traceSegment_028_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_028 216 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 216 108 108, g32p_row04_traceSegment_028_0216_0108, g32p_row04_traceSegment_028_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_028 0 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 0 216 216, g32p_row04_traceSegment_028_0000_0216, g32p_row04_traceSegment_028_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 432 13 14, g32p_row04_traceSegment_028_0432_0013, g32p_row04_traceSegment_028_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 459 13 14, g32p_row04_traceSegment_028_0459_0013, g32p_row04_traceSegment_028_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 432 27 27, g32p_row04_traceSegment_028_0432_0027, g32p_row04_traceSegment_028_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 486 13 14, g32p_row04_traceSegment_028_0486_0013, g32p_row04_traceSegment_028_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 513 13 14, g32p_row04_traceSegment_028_0513_0013, g32p_row04_traceSegment_028_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 486 27 27, g32p_row04_traceSegment_028_0486_0027, g32p_row04_traceSegment_028_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 432 54 54, g32p_row04_traceSegment_028_0432_0054, g32p_row04_traceSegment_028_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 540 13 14, g32p_row04_traceSegment_028_0540_0013, g32p_row04_traceSegment_028_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 567 13 14, g32p_row04_traceSegment_028_0567_0013, g32p_row04_traceSegment_028_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 540 27 27, g32p_row04_traceSegment_028_0540_0027, g32p_row04_traceSegment_028_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 594 13 14, g32p_row04_traceSegment_028_0594_0013, g32p_row04_traceSegment_028_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 621 13 14, g32p_row04_traceSegment_028_0621_0013, g32p_row04_traceSegment_028_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 594 27 27, g32p_row04_traceSegment_028_0594_0027, g32p_row04_traceSegment_028_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 540 54 54, g32p_row04_traceSegment_028_0540_0054, g32p_row04_traceSegment_028_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_028 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 432 108 108, g32p_row04_traceSegment_028_0432_0108, g32p_row04_traceSegment_028_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 648 13 14, g32p_row04_traceSegment_028_0648_0013, g32p_row04_traceSegment_028_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 675 13 14, g32p_row04_traceSegment_028_0675_0013, g32p_row04_traceSegment_028_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 648 27 27, g32p_row04_traceSegment_028_0648_0027, g32p_row04_traceSegment_028_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 702 13 14, g32p_row04_traceSegment_028_0702_0013, g32p_row04_traceSegment_028_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 729 13 14, g32p_row04_traceSegment_028_0729_0013, g32p_row04_traceSegment_028_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 702 27 27, g32p_row04_traceSegment_028_0702_0027, g32p_row04_traceSegment_028_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 648 54 54, g32p_row04_traceSegment_028_0648_0054, g32p_row04_traceSegment_028_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 756 13 14, g32p_row04_traceSegment_028_0756_0013, g32p_row04_traceSegment_028_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 783 13 14, g32p_row04_traceSegment_028_0783_0013, g32p_row04_traceSegment_028_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 756 27 27, g32p_row04_traceSegment_028_0756_0027, g32p_row04_traceSegment_028_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 810 13 14, g32p_row04_traceSegment_028_0810_0013, g32p_row04_traceSegment_028_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 837 13 14, g32p_row04_traceSegment_028_0837_0013, g32p_row04_traceSegment_028_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 810 27 27, g32p_row04_traceSegment_028_0810_0027, g32p_row04_traceSegment_028_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 756 54 54, g32p_row04_traceSegment_028_0756_0054, g32p_row04_traceSegment_028_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_028 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 648 108 108, g32p_row04_traceSegment_028_0648_0108, g32p_row04_traceSegment_028_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_028 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 432 216 216, g32p_row04_traceSegment_028_0432_0216, g32p_row04_traceSegment_028_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_028 0 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 0 432 432, g32p_row04_traceSegment_028_0000_0432, g32p_row04_traceSegment_028_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 864 13 14, g32p_row04_traceSegment_028_0864_0013, g32p_row04_traceSegment_028_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 891 13 14, g32p_row04_traceSegment_028_0891_0013, g32p_row04_traceSegment_028_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 864 27 27, g32p_row04_traceSegment_028_0864_0027, g32p_row04_traceSegment_028_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 918 13 14, g32p_row04_traceSegment_028_0918_0013, g32p_row04_traceSegment_028_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 945 13 14, g32p_row04_traceSegment_028_0945_0013, g32p_row04_traceSegment_028_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 918 27 27, g32p_row04_traceSegment_028_0918_0027, g32p_row04_traceSegment_028_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 864 54 54, g32p_row04_traceSegment_028_0864_0054, g32p_row04_traceSegment_028_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 972 13 14, g32p_row04_traceSegment_028_0972_0013, g32p_row04_traceSegment_028_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 999 13 14, g32p_row04_traceSegment_028_0999_0013, g32p_row04_traceSegment_028_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 972 27 27, g32p_row04_traceSegment_028_0972_0027, g32p_row04_traceSegment_028_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1026 13 14, g32p_row04_traceSegment_028_1026_0013, g32p_row04_traceSegment_028_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1053 13 14, g32p_row04_traceSegment_028_1053_0013, g32p_row04_traceSegment_028_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1026 27 27, g32p_row04_traceSegment_028_1026_0027, g32p_row04_traceSegment_028_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 972 54 54, g32p_row04_traceSegment_028_0972_0054, g32p_row04_traceSegment_028_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_028 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 864 108 108, g32p_row04_traceSegment_028_0864_0108, g32p_row04_traceSegment_028_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1080 13 14, g32p_row04_traceSegment_028_1080_0013, g32p_row04_traceSegment_028_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1107 13 14, g32p_row04_traceSegment_028_1107_0013, g32p_row04_traceSegment_028_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1080 27 27, g32p_row04_traceSegment_028_1080_0027, g32p_row04_traceSegment_028_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1134 13 14, g32p_row04_traceSegment_028_1134_0013, g32p_row04_traceSegment_028_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1161 13 14, g32p_row04_traceSegment_028_1161_0013, g32p_row04_traceSegment_028_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1134 27 27, g32p_row04_traceSegment_028_1134_0027, g32p_row04_traceSegment_028_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1080 54 54, g32p_row04_traceSegment_028_1080_0054, g32p_row04_traceSegment_028_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1188 13 14, g32p_row04_traceSegment_028_1188_0013, g32p_row04_traceSegment_028_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1215 13 14, g32p_row04_traceSegment_028_1215_0013, g32p_row04_traceSegment_028_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1188 27 27, g32p_row04_traceSegment_028_1188_0027, g32p_row04_traceSegment_028_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1242 13 14, g32p_row04_traceSegment_028_1242_0013, g32p_row04_traceSegment_028_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1269 13 14, g32p_row04_traceSegment_028_1269_0013, g32p_row04_traceSegment_028_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1242 27 27, g32p_row04_traceSegment_028_1242_0027, g32p_row04_traceSegment_028_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1188 54 54, g32p_row04_traceSegment_028_1188_0054, g32p_row04_traceSegment_028_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_028 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1080 108 108, g32p_row04_traceSegment_028_1080_0108, g32p_row04_traceSegment_028_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_028 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 864 216 216, g32p_row04_traceSegment_028_0864_0216, g32p_row04_traceSegment_028_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1296 13 14, g32p_row04_traceSegment_028_1296_0013, g32p_row04_traceSegment_028_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1323 13 14, g32p_row04_traceSegment_028_1323_0013, g32p_row04_traceSegment_028_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1296 27 27, g32p_row04_traceSegment_028_1296_0027, g32p_row04_traceSegment_028_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1350 13 14, g32p_row04_traceSegment_028_1350_0013, g32p_row04_traceSegment_028_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1377 13 14, g32p_row04_traceSegment_028_1377_0013, g32p_row04_traceSegment_028_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1350 27 27, g32p_row04_traceSegment_028_1350_0027, g32p_row04_traceSegment_028_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1296 54 54, g32p_row04_traceSegment_028_1296_0054, g32p_row04_traceSegment_028_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1404 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1404 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1404 13 14, g32p_row04_traceSegment_028_1404_0013, g32p_row04_traceSegment_028_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1431 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1431 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1431 13 14, g32p_row04_traceSegment_028_1431_0013, g32p_row04_traceSegment_028_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1404 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1404 27 27, g32p_row04_traceSegment_028_1404_0027, g32p_row04_traceSegment_028_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1471 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1458 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1458 13 14, g32p_row04_traceSegment_028_1458_0013, g32p_row04_traceSegment_028_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1485 13 14, g32p_row04_traceSegment_028_1485_0013, g32p_row04_traceSegment_028_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1458 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1458 27 27, g32p_row04_traceSegment_028_1458_0027, g32p_row04_traceSegment_028_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 1404 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1404 54 54, g32p_row04_traceSegment_028_1404_0054, g32p_row04_traceSegment_028_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_028 1296 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1296 108 108, g32p_row04_traceSegment_028_1296_0108, g32p_row04_traceSegment_028_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1512 13 14, g32p_row04_traceSegment_028_1512_0013, g32p_row04_traceSegment_028_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1539 13 14, g32p_row04_traceSegment_028_1539_0013, g32p_row04_traceSegment_028_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1512 27 27, g32p_row04_traceSegment_028_1512_0027, g32p_row04_traceSegment_028_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1566 13 14, g32p_row04_traceSegment_028_1566_0013, g32p_row04_traceSegment_028_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1593 13 14, g32p_row04_traceSegment_028_1593_0013, g32p_row04_traceSegment_028_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1566 27 27, g32p_row04_traceSegment_028_1566_0027, g32p_row04_traceSegment_028_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1512 54 54, g32p_row04_traceSegment_028_1512_0054, g32p_row04_traceSegment_028_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1620 13 14, g32p_row04_traceSegment_028_1620_0013, g32p_row04_traceSegment_028_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1647 13 14, g32p_row04_traceSegment_028_1647_0013, g32p_row04_traceSegment_028_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1620 27 27, g32p_row04_traceSegment_028_1620_0027, g32p_row04_traceSegment_028_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1674 13 14, g32p_row04_traceSegment_028_1674_0013, g32p_row04_traceSegment_028_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_028 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_028 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_028_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_028 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1701 13 14, g32p_row04_traceSegment_028_1701_0013, g32p_row04_traceSegment_028_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_028 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1674 27 27, g32p_row04_traceSegment_028_1674_0027, g32p_row04_traceSegment_028_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_028 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1620 54 54, g32p_row04_traceSegment_028_1620_0054, g32p_row04_traceSegment_028_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_028 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1512 108 108, g32p_row04_traceSegment_028_1512_0108, g32p_row04_traceSegment_028_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_028_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_028 1296 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 1296 216 216, g32p_row04_traceSegment_028_1296_0216, g32p_row04_traceSegment_028_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_028 864 864 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 864 432 432, g32p_row04_traceSegment_028_0864_0432, g32p_row04_traceSegment_028_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_028_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_028 0 1728 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_028 0 864 864, g32p_row04_traceSegment_028_0000_0864, g32p_row04_traceSegment_028_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 28 = [0, 4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_028_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_029 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 29 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_029_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 0 13 14, g32p_row04_traceSegment_029_0000_0013, g32p_row04_traceSegment_029_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 27 13 14, g32p_row04_traceSegment_029_0027_0013, g32p_row04_traceSegment_029_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 0 27 27, g32p_row04_traceSegment_029_0000_0027, g32p_row04_traceSegment_029_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 54 13 14, g32p_row04_traceSegment_029_0054_0013, g32p_row04_traceSegment_029_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 81 13 14, g32p_row04_traceSegment_029_0081_0013, g32p_row04_traceSegment_029_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 54 27 27, g32p_row04_traceSegment_029_0054_0027, g32p_row04_traceSegment_029_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 0 54 54, g32p_row04_traceSegment_029_0000_0054, g32p_row04_traceSegment_029_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 108 13 14, g32p_row04_traceSegment_029_0108_0013, g32p_row04_traceSegment_029_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 135 13 14, g32p_row04_traceSegment_029_0135_0013, g32p_row04_traceSegment_029_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 108 27 27, g32p_row04_traceSegment_029_0108_0027, g32p_row04_traceSegment_029_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 162 13 14, g32p_row04_traceSegment_029_0162_0013, g32p_row04_traceSegment_029_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 189 13 14, g32p_row04_traceSegment_029_0189_0013, g32p_row04_traceSegment_029_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 162 27 27, g32p_row04_traceSegment_029_0162_0027, g32p_row04_traceSegment_029_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 108 54 54, g32p_row04_traceSegment_029_0108_0054, g32p_row04_traceSegment_029_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_029 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 0 108 108, g32p_row04_traceSegment_029_0000_0108, g32p_row04_traceSegment_029_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 216 13 14, g32p_row04_traceSegment_029_0216_0013, g32p_row04_traceSegment_029_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 243 13 14, g32p_row04_traceSegment_029_0243_0013, g32p_row04_traceSegment_029_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 216 27 27, g32p_row04_traceSegment_029_0216_0027, g32p_row04_traceSegment_029_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 270 13 14, g32p_row04_traceSegment_029_0270_0013, g32p_row04_traceSegment_029_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 297 13 14, g32p_row04_traceSegment_029_0297_0013, g32p_row04_traceSegment_029_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 270 27 27, g32p_row04_traceSegment_029_0270_0027, g32p_row04_traceSegment_029_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 216 54 54, g32p_row04_traceSegment_029_0216_0054, g32p_row04_traceSegment_029_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 324 13 14, g32p_row04_traceSegment_029_0324_0013, g32p_row04_traceSegment_029_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 351 13 14, g32p_row04_traceSegment_029_0351_0013, g32p_row04_traceSegment_029_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 324 27 27, g32p_row04_traceSegment_029_0324_0027, g32p_row04_traceSegment_029_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 378 13 14, g32p_row04_traceSegment_029_0378_0013, g32p_row04_traceSegment_029_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 405 13 14, g32p_row04_traceSegment_029_0405_0013, g32p_row04_traceSegment_029_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 378 27 27, g32p_row04_traceSegment_029_0378_0027, g32p_row04_traceSegment_029_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 324 54 54, g32p_row04_traceSegment_029_0324_0054, g32p_row04_traceSegment_029_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_029 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 216 108 108, g32p_row04_traceSegment_029_0216_0108, g32p_row04_traceSegment_029_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_029 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 0 216 216, g32p_row04_traceSegment_029_0000_0216, g32p_row04_traceSegment_029_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 432 13 14, g32p_row04_traceSegment_029_0432_0013, g32p_row04_traceSegment_029_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 459 13 14, g32p_row04_traceSegment_029_0459_0013, g32p_row04_traceSegment_029_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 432 27 27, g32p_row04_traceSegment_029_0432_0027, g32p_row04_traceSegment_029_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 486 13 14, g32p_row04_traceSegment_029_0486_0013, g32p_row04_traceSegment_029_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 513 13 14, g32p_row04_traceSegment_029_0513_0013, g32p_row04_traceSegment_029_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 486 27 27, g32p_row04_traceSegment_029_0486_0027, g32p_row04_traceSegment_029_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 432 54 54, g32p_row04_traceSegment_029_0432_0054, g32p_row04_traceSegment_029_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 540 13 14, g32p_row04_traceSegment_029_0540_0013, g32p_row04_traceSegment_029_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 567 13 14, g32p_row04_traceSegment_029_0567_0013, g32p_row04_traceSegment_029_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 540 27 27, g32p_row04_traceSegment_029_0540_0027, g32p_row04_traceSegment_029_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 594 13 14, g32p_row04_traceSegment_029_0594_0013, g32p_row04_traceSegment_029_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 621 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 634 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 621 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 621 13 14, g32p_row04_traceSegment_029_0621_0013, g32p_row04_traceSegment_029_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 594 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 594 27 27, g32p_row04_traceSegment_029_0594_0027, g32p_row04_traceSegment_029_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 540 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 540 54 54, g32p_row04_traceSegment_029_0540_0054, g32p_row04_traceSegment_029_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_029 432 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 432 108 108, g32p_row04_traceSegment_029_0432_0108, g32p_row04_traceSegment_029_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 648 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 661 14 = [5] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 648 27 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 648 13 14, g32p_row04_traceSegment_029_0648_0013, g32p_row04_traceSegment_029_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 675 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 688 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 675 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 675 13 14, g32p_row04_traceSegment_029_0675_0013, g32p_row04_traceSegment_029_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 648 54 = [11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 648 27 27, g32p_row04_traceSegment_029_0648_0027, g32p_row04_traceSegment_029_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 702 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 702 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 702 13 14, g32p_row04_traceSegment_029_0702_0013, g32p_row04_traceSegment_029_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 729 13 = [4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 742 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 729 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 729 13 14, g32p_row04_traceSegment_029_0729_0013, g32p_row04_traceSegment_029_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 702 54 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 702 27 27, g32p_row04_traceSegment_029_0702_0027, g32p_row04_traceSegment_029_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 648 108 = [17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 648 54 54, g32p_row04_traceSegment_029_0648_0054, g32p_row04_traceSegment_029_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 756 13 14, g32p_row04_traceSegment_029_0756_0013, g32p_row04_traceSegment_029_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 783 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 796 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 783 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 783 13 14, g32p_row04_traceSegment_029_0783_0013, g32p_row04_traceSegment_029_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 756 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 756 27 27, g32p_row04_traceSegment_029_0756_0027, g32p_row04_traceSegment_029_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 810 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 810 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 810 13 14, g32p_row04_traceSegment_029_0810_0013, g32p_row04_traceSegment_029_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 837 13 14, g32p_row04_traceSegment_029_0837_0013, g32p_row04_traceSegment_029_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 810 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 810 27 27, g32p_row04_traceSegment_029_0810_0027, g32p_row04_traceSegment_029_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 756 108 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 756 54 54, g32p_row04_traceSegment_029_0756_0054, g32p_row04_traceSegment_029_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_029 648 216 = [22] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 648 108 108, g32p_row04_traceSegment_029_0648_0108, g32p_row04_traceSegment_029_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_029 432 432 = [26] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 432 216 216, g32p_row04_traceSegment_029_0432_0216, g32p_row04_traceSegment_029_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_029 0 864 = [26] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 0 432 432, g32p_row04_traceSegment_029_0000_0432, g32p_row04_traceSegment_029_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 864 13 14, g32p_row04_traceSegment_029_0864_0013, g32p_row04_traceSegment_029_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 891 13 14, g32p_row04_traceSegment_029_0891_0013, g32p_row04_traceSegment_029_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 864 27 27, g32p_row04_traceSegment_029_0864_0027, g32p_row04_traceSegment_029_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 918 13 14, g32p_row04_traceSegment_029_0918_0013, g32p_row04_traceSegment_029_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 945 13 14, g32p_row04_traceSegment_029_0945_0013, g32p_row04_traceSegment_029_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 918 27 27, g32p_row04_traceSegment_029_0918_0027, g32p_row04_traceSegment_029_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 864 54 54, g32p_row04_traceSegment_029_0864_0054, g32p_row04_traceSegment_029_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 972 13 14, g32p_row04_traceSegment_029_0972_0013, g32p_row04_traceSegment_029_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 999 13 14, g32p_row04_traceSegment_029_0999_0013, g32p_row04_traceSegment_029_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 972 27 27, g32p_row04_traceSegment_029_0972_0027, g32p_row04_traceSegment_029_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1026 13 14, g32p_row04_traceSegment_029_1026_0013, g32p_row04_traceSegment_029_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1053 13 14, g32p_row04_traceSegment_029_1053_0013, g32p_row04_traceSegment_029_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1026 27 27, g32p_row04_traceSegment_029_1026_0027, g32p_row04_traceSegment_029_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 972 54 54, g32p_row04_traceSegment_029_0972_0054, g32p_row04_traceSegment_029_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_029 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 864 108 108, g32p_row04_traceSegment_029_0864_0108, g32p_row04_traceSegment_029_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1080 13 14, g32p_row04_traceSegment_029_1080_0013, g32p_row04_traceSegment_029_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1107 13 14, g32p_row04_traceSegment_029_1107_0013, g32p_row04_traceSegment_029_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1080 27 27, g32p_row04_traceSegment_029_1080_0027, g32p_row04_traceSegment_029_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1134 13 14, g32p_row04_traceSegment_029_1134_0013, g32p_row04_traceSegment_029_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1161 13 14, g32p_row04_traceSegment_029_1161_0013, g32p_row04_traceSegment_029_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1134 27 27, g32p_row04_traceSegment_029_1134_0027, g32p_row04_traceSegment_029_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1080 54 54, g32p_row04_traceSegment_029_1080_0054, g32p_row04_traceSegment_029_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1188 13 14, g32p_row04_traceSegment_029_1188_0013, g32p_row04_traceSegment_029_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1215 13 14, g32p_row04_traceSegment_029_1215_0013, g32p_row04_traceSegment_029_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1188 27 27, g32p_row04_traceSegment_029_1188_0027, g32p_row04_traceSegment_029_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1242 13 14, g32p_row04_traceSegment_029_1242_0013, g32p_row04_traceSegment_029_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1269 13 14, g32p_row04_traceSegment_029_1269_0013, g32p_row04_traceSegment_029_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1242 27 27, g32p_row04_traceSegment_029_1242_0027, g32p_row04_traceSegment_029_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1188 54 54, g32p_row04_traceSegment_029_1188_0054, g32p_row04_traceSegment_029_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_029 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1080 108 108, g32p_row04_traceSegment_029_1080_0108, g32p_row04_traceSegment_029_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_029 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 864 216 216, g32p_row04_traceSegment_029_0864_0216, g32p_row04_traceSegment_029_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1296 13 14, g32p_row04_traceSegment_029_1296_0013, g32p_row04_traceSegment_029_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1323 13 14, g32p_row04_traceSegment_029_1323_0013, g32p_row04_traceSegment_029_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1296 27 27, g32p_row04_traceSegment_029_1296_0027, g32p_row04_traceSegment_029_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1350 13 14, g32p_row04_traceSegment_029_1350_0013, g32p_row04_traceSegment_029_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1377 13 14, g32p_row04_traceSegment_029_1377_0013, g32p_row04_traceSegment_029_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1350 27 27, g32p_row04_traceSegment_029_1350_0027, g32p_row04_traceSegment_029_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1296 54 54, g32p_row04_traceSegment_029_1296_0054, g32p_row04_traceSegment_029_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1404 13 14, g32p_row04_traceSegment_029_1404_0013, g32p_row04_traceSegment_029_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1431 13 14, g32p_row04_traceSegment_029_1431_0013, g32p_row04_traceSegment_029_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1404 27 27, g32p_row04_traceSegment_029_1404_0027, g32p_row04_traceSegment_029_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1458 13 14, g32p_row04_traceSegment_029_1458_0013, g32p_row04_traceSegment_029_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1485 13 14, g32p_row04_traceSegment_029_1485_0013, g32p_row04_traceSegment_029_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1458 27 27, g32p_row04_traceSegment_029_1458_0027, g32p_row04_traceSegment_029_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1404 54 54, g32p_row04_traceSegment_029_1404_0054, g32p_row04_traceSegment_029_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_029 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1296 108 108, g32p_row04_traceSegment_029_1296_0108, g32p_row04_traceSegment_029_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1512 13 14, g32p_row04_traceSegment_029_1512_0013, g32p_row04_traceSegment_029_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1552 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1539 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1539 13 14, g32p_row04_traceSegment_029_1539_0013, g32p_row04_traceSegment_029_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1512 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1512 27 27, g32p_row04_traceSegment_029_1512_0027, g32p_row04_traceSegment_029_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1566 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1566 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1566 13 14, g32p_row04_traceSegment_029_1566_0013, g32p_row04_traceSegment_029_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1593 13 14, g32p_row04_traceSegment_029_1593_0013, g32p_row04_traceSegment_029_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1566 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1566 27 27, g32p_row04_traceSegment_029_1566_0027, g32p_row04_traceSegment_029_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 1512 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1512 54 54, g32p_row04_traceSegment_029_1512_0054, g32p_row04_traceSegment_029_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1620 13 14, g32p_row04_traceSegment_029_1620_0013, g32p_row04_traceSegment_029_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1660 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1647 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1647 13 14, g32p_row04_traceSegment_029_1647_0013, g32p_row04_traceSegment_029_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1620 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1620 27 27, g32p_row04_traceSegment_029_1620_0027, g32p_row04_traceSegment_029_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1674 13 14, g32p_row04_traceSegment_029_1674_0013, g32p_row04_traceSegment_029_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_029 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_029 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_029_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_029 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1701 13 14, g32p_row04_traceSegment_029_1701_0013, g32p_row04_traceSegment_029_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_029 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1674 27 27, g32p_row04_traceSegment_029_1674_0027, g32p_row04_traceSegment_029_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_029 1620 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1620 54 54, g32p_row04_traceSegment_029_1620_0054, g32p_row04_traceSegment_029_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_029 1512 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1512 108 108, g32p_row04_traceSegment_029_1512_0108, g32p_row04_traceSegment_029_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_029_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_029 1296 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 1296 216 216, g32p_row04_traceSegment_029_1296_0216, g32p_row04_traceSegment_029_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_029 864 864 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 864 432 432, g32p_row04_traceSegment_029_0864_0432, g32p_row04_traceSegment_029_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_029_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_029 0 1728 = [32] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_029 0 864 864, g32p_row04_traceSegment_029_0000_0864, g32p_row04_traceSegment_029_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 29 = [32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_029_0000_1728

end HodgeLean.Foundations.Program

end
end
