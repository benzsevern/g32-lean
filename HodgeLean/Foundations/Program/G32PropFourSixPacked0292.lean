import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_000 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 0 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_000_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 0 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 0 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 0 13 14, g32p_row02_traceSegment_000_0000_0013, g32p_row02_traceSegment_000_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 27 13 14, g32p_row02_traceSegment_000_0027_0013, g32p_row02_traceSegment_000_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 0 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 0 27 27, g32p_row02_traceSegment_000_0000_0027, g32p_row02_traceSegment_000_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 54 13 14, g32p_row02_traceSegment_000_0054_0013, g32p_row02_traceSegment_000_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 81 13 14, g32p_row02_traceSegment_000_0081_0013, g32p_row02_traceSegment_000_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 54 27 27, g32p_row02_traceSegment_000_0054_0027, g32p_row02_traceSegment_000_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 0 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 0 54 54, g32p_row02_traceSegment_000_0000_0054, g32p_row02_traceSegment_000_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 108 13 14, g32p_row02_traceSegment_000_0108_0013, g32p_row02_traceSegment_000_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 135 13 14, g32p_row02_traceSegment_000_0135_0013, g32p_row02_traceSegment_000_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 108 27 27, g32p_row02_traceSegment_000_0108_0027, g32p_row02_traceSegment_000_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 162 13 14, g32p_row02_traceSegment_000_0162_0013, g32p_row02_traceSegment_000_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 189 13 14, g32p_row02_traceSegment_000_0189_0013, g32p_row02_traceSegment_000_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 162 27 27, g32p_row02_traceSegment_000_0162_0027, g32p_row02_traceSegment_000_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 108 54 54, g32p_row02_traceSegment_000_0108_0054, g32p_row02_traceSegment_000_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 0 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 0 108 108, g32p_row02_traceSegment_000_0000_0108, g32p_row02_traceSegment_000_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 216 13 14, g32p_row02_traceSegment_000_0216_0013, g32p_row02_traceSegment_000_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 243 13 14, g32p_row02_traceSegment_000_0243_0013, g32p_row02_traceSegment_000_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 216 27 27, g32p_row02_traceSegment_000_0216_0027, g32p_row02_traceSegment_000_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 270 13 14, g32p_row02_traceSegment_000_0270_0013, g32p_row02_traceSegment_000_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 297 13 14, g32p_row02_traceSegment_000_0297_0013, g32p_row02_traceSegment_000_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 270 27 27, g32p_row02_traceSegment_000_0270_0027, g32p_row02_traceSegment_000_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 216 54 54, g32p_row02_traceSegment_000_0216_0054, g32p_row02_traceSegment_000_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 324 13 14, g32p_row02_traceSegment_000_0324_0013, g32p_row02_traceSegment_000_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 351 13 14, g32p_row02_traceSegment_000_0351_0013, g32p_row02_traceSegment_000_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 324 27 27, g32p_row02_traceSegment_000_0324_0027, g32p_row02_traceSegment_000_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 378 13 14, g32p_row02_traceSegment_000_0378_0013, g32p_row02_traceSegment_000_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 405 13 14, g32p_row02_traceSegment_000_0405_0013, g32p_row02_traceSegment_000_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 378 27 27, g32p_row02_traceSegment_000_0378_0027, g32p_row02_traceSegment_000_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 324 54 54, g32p_row02_traceSegment_000_0324_0054, g32p_row02_traceSegment_000_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 216 108 108, g32p_row02_traceSegment_000_0216_0108, g32p_row02_traceSegment_000_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_000 0 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 0 216 216, g32p_row02_traceSegment_000_0000_0216, g32p_row02_traceSegment_000_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 432 13 14, g32p_row02_traceSegment_000_0432_0013, g32p_row02_traceSegment_000_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 459 13 14, g32p_row02_traceSegment_000_0459_0013, g32p_row02_traceSegment_000_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 432 27 27, g32p_row02_traceSegment_000_0432_0027, g32p_row02_traceSegment_000_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 486 13 14, g32p_row02_traceSegment_000_0486_0013, g32p_row02_traceSegment_000_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 513 13 14, g32p_row02_traceSegment_000_0513_0013, g32p_row02_traceSegment_000_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 486 27 27, g32p_row02_traceSegment_000_0486_0027, g32p_row02_traceSegment_000_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 432 54 54, g32p_row02_traceSegment_000_0432_0054, g32p_row02_traceSegment_000_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 540 13 14, g32p_row02_traceSegment_000_0540_0013, g32p_row02_traceSegment_000_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 567 13 14, g32p_row02_traceSegment_000_0567_0013, g32p_row02_traceSegment_000_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 540 27 27, g32p_row02_traceSegment_000_0540_0027, g32p_row02_traceSegment_000_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 594 13 14, g32p_row02_traceSegment_000_0594_0013, g32p_row02_traceSegment_000_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 621 13 14, g32p_row02_traceSegment_000_0621_0013, g32p_row02_traceSegment_000_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 594 27 27, g32p_row02_traceSegment_000_0594_0027, g32p_row02_traceSegment_000_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 540 54 54, g32p_row02_traceSegment_000_0540_0054, g32p_row02_traceSegment_000_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 432 108 108, g32p_row02_traceSegment_000_0432_0108, g32p_row02_traceSegment_000_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 648 13 14, g32p_row02_traceSegment_000_0648_0013, g32p_row02_traceSegment_000_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 675 13 14, g32p_row02_traceSegment_000_0675_0013, g32p_row02_traceSegment_000_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 648 27 27, g32p_row02_traceSegment_000_0648_0027, g32p_row02_traceSegment_000_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 702 13 14, g32p_row02_traceSegment_000_0702_0013, g32p_row02_traceSegment_000_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 729 13 14, g32p_row02_traceSegment_000_0729_0013, g32p_row02_traceSegment_000_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 702 27 27, g32p_row02_traceSegment_000_0702_0027, g32p_row02_traceSegment_000_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 648 54 54, g32p_row02_traceSegment_000_0648_0054, g32p_row02_traceSegment_000_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 756 13 14, g32p_row02_traceSegment_000_0756_0013, g32p_row02_traceSegment_000_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 783 13 14, g32p_row02_traceSegment_000_0783_0013, g32p_row02_traceSegment_000_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 756 27 27, g32p_row02_traceSegment_000_0756_0027, g32p_row02_traceSegment_000_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 810 13 14, g32p_row02_traceSegment_000_0810_0013, g32p_row02_traceSegment_000_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 837 13 14, g32p_row02_traceSegment_000_0837_0013, g32p_row02_traceSegment_000_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 810 27 27, g32p_row02_traceSegment_000_0810_0027, g32p_row02_traceSegment_000_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 756 54 54, g32p_row02_traceSegment_000_0756_0054, g32p_row02_traceSegment_000_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 648 108 108, g32p_row02_traceSegment_000_0648_0108, g32p_row02_traceSegment_000_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_000 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 432 216 216, g32p_row02_traceSegment_000_0432_0216, g32p_row02_traceSegment_000_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_000 0 864 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 0 432 432, g32p_row02_traceSegment_000_0000_0432, g32p_row02_traceSegment_000_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 864 13 14, g32p_row02_traceSegment_000_0864_0013, g32p_row02_traceSegment_000_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 891 13 14, g32p_row02_traceSegment_000_0891_0013, g32p_row02_traceSegment_000_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 864 27 27, g32p_row02_traceSegment_000_0864_0027, g32p_row02_traceSegment_000_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 918 13 14, g32p_row02_traceSegment_000_0918_0013, g32p_row02_traceSegment_000_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 945 13 14, g32p_row02_traceSegment_000_0945_0013, g32p_row02_traceSegment_000_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 918 27 27, g32p_row02_traceSegment_000_0918_0027, g32p_row02_traceSegment_000_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 864 54 54, g32p_row02_traceSegment_000_0864_0054, g32p_row02_traceSegment_000_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 972 13 14, g32p_row02_traceSegment_000_0972_0013, g32p_row02_traceSegment_000_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 999 13 14, g32p_row02_traceSegment_000_0999_0013, g32p_row02_traceSegment_000_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 972 27 27, g32p_row02_traceSegment_000_0972_0027, g32p_row02_traceSegment_000_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1026 13 14, g32p_row02_traceSegment_000_1026_0013, g32p_row02_traceSegment_000_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1053 13 14, g32p_row02_traceSegment_000_1053_0013, g32p_row02_traceSegment_000_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1026 27 27, g32p_row02_traceSegment_000_1026_0027, g32p_row02_traceSegment_000_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 972 54 54, g32p_row02_traceSegment_000_0972_0054, g32p_row02_traceSegment_000_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 864 108 108, g32p_row02_traceSegment_000_0864_0108, g32p_row02_traceSegment_000_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1080 13 14, g32p_row02_traceSegment_000_1080_0013, g32p_row02_traceSegment_000_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1107 13 14, g32p_row02_traceSegment_000_1107_0013, g32p_row02_traceSegment_000_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1080 27 27, g32p_row02_traceSegment_000_1080_0027, g32p_row02_traceSegment_000_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1134 13 14, g32p_row02_traceSegment_000_1134_0013, g32p_row02_traceSegment_000_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1161 13 14, g32p_row02_traceSegment_000_1161_0013, g32p_row02_traceSegment_000_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1134 27 27, g32p_row02_traceSegment_000_1134_0027, g32p_row02_traceSegment_000_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1080 54 54, g32p_row02_traceSegment_000_1080_0054, g32p_row02_traceSegment_000_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1188 13 14, g32p_row02_traceSegment_000_1188_0013, g32p_row02_traceSegment_000_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1215 13 14, g32p_row02_traceSegment_000_1215_0013, g32p_row02_traceSegment_000_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1188 27 27, g32p_row02_traceSegment_000_1188_0027, g32p_row02_traceSegment_000_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1242 13 14, g32p_row02_traceSegment_000_1242_0013, g32p_row02_traceSegment_000_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1269 13 14, g32p_row02_traceSegment_000_1269_0013, g32p_row02_traceSegment_000_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1242 27 27, g32p_row02_traceSegment_000_1242_0027, g32p_row02_traceSegment_000_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1188 54 54, g32p_row02_traceSegment_000_1188_0054, g32p_row02_traceSegment_000_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1080 108 108, g32p_row02_traceSegment_000_1080_0108, g32p_row02_traceSegment_000_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_000 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 864 216 216, g32p_row02_traceSegment_000_0864_0216, g32p_row02_traceSegment_000_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1296 13 14, g32p_row02_traceSegment_000_1296_0013, g32p_row02_traceSegment_000_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1323 13 14, g32p_row02_traceSegment_000_1323_0013, g32p_row02_traceSegment_000_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1296 27 27, g32p_row02_traceSegment_000_1296_0027, g32p_row02_traceSegment_000_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1350 13 14, g32p_row02_traceSegment_000_1350_0013, g32p_row02_traceSegment_000_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1377 13 14, g32p_row02_traceSegment_000_1377_0013, g32p_row02_traceSegment_000_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1350 27 27, g32p_row02_traceSegment_000_1350_0027, g32p_row02_traceSegment_000_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1296 54 54, g32p_row02_traceSegment_000_1296_0054, g32p_row02_traceSegment_000_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1404 13 14, g32p_row02_traceSegment_000_1404_0013, g32p_row02_traceSegment_000_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1431 13 14, g32p_row02_traceSegment_000_1431_0013, g32p_row02_traceSegment_000_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1404 27 27, g32p_row02_traceSegment_000_1404_0027, g32p_row02_traceSegment_000_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1458 13 14, g32p_row02_traceSegment_000_1458_0013, g32p_row02_traceSegment_000_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1485 13 14, g32p_row02_traceSegment_000_1485_0013, g32p_row02_traceSegment_000_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1458 27 27, g32p_row02_traceSegment_000_1458_0027, g32p_row02_traceSegment_000_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1404 54 54, g32p_row02_traceSegment_000_1404_0054, g32p_row02_traceSegment_000_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1296 108 108, g32p_row02_traceSegment_000_1296_0108, g32p_row02_traceSegment_000_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1512 13 14, g32p_row02_traceSegment_000_1512_0013, g32p_row02_traceSegment_000_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1539 13 14, g32p_row02_traceSegment_000_1539_0013, g32p_row02_traceSegment_000_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1512 27 27, g32p_row02_traceSegment_000_1512_0027, g32p_row02_traceSegment_000_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1566 13 14, g32p_row02_traceSegment_000_1566_0013, g32p_row02_traceSegment_000_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1593 13 14, g32p_row02_traceSegment_000_1593_0013, g32p_row02_traceSegment_000_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1566 27 27, g32p_row02_traceSegment_000_1566_0027, g32p_row02_traceSegment_000_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1512 54 54, g32p_row02_traceSegment_000_1512_0054, g32p_row02_traceSegment_000_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1620 13 14, g32p_row02_traceSegment_000_1620_0013, g32p_row02_traceSegment_000_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1647 13 14, g32p_row02_traceSegment_000_1647_0013, g32p_row02_traceSegment_000_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1620 27 27, g32p_row02_traceSegment_000_1620_0027, g32p_row02_traceSegment_000_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1674 13 14, g32p_row02_traceSegment_000_1674_0013, g32p_row02_traceSegment_000_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1701 13 14, g32p_row02_traceSegment_000_1701_0013, g32p_row02_traceSegment_000_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1674 27 27, g32p_row02_traceSegment_000_1674_0027, g32p_row02_traceSegment_000_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1620 54 54, g32p_row02_traceSegment_000_1620_0054, g32p_row02_traceSegment_000_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1512 108 108, g32p_row02_traceSegment_000_1512_0108, g32p_row02_traceSegment_000_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_000 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1296 216 216, g32p_row02_traceSegment_000_1296_0216, g32p_row02_traceSegment_000_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_000 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 864 432 432, g32p_row02_traceSegment_000_0864_0432, g32p_row02_traceSegment_000_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_000 0 1728 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 0 864 864, g32p_row02_traceSegment_000_0000_0864, g32p_row02_traceSegment_000_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1728 13 14, g32p_row02_traceSegment_000_1728_0013, g32p_row02_traceSegment_000_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1755 13 14, g32p_row02_traceSegment_000_1755_0013, g32p_row02_traceSegment_000_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1728 27 27, g32p_row02_traceSegment_000_1728_0027, g32p_row02_traceSegment_000_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1782 13 14, g32p_row02_traceSegment_000_1782_0013, g32p_row02_traceSegment_000_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1809 13 14, g32p_row02_traceSegment_000_1809_0013, g32p_row02_traceSegment_000_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1782 27 27, g32p_row02_traceSegment_000_1782_0027, g32p_row02_traceSegment_000_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1728 54 54, g32p_row02_traceSegment_000_1728_0054, g32p_row02_traceSegment_000_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1836 13 14, g32p_row02_traceSegment_000_1836_0013, g32p_row02_traceSegment_000_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1863 13 14, g32p_row02_traceSegment_000_1863_0013, g32p_row02_traceSegment_000_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1836 27 27, g32p_row02_traceSegment_000_1836_0027, g32p_row02_traceSegment_000_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1890 13 14, g32p_row02_traceSegment_000_1890_0013, g32p_row02_traceSegment_000_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1917 13 14, g32p_row02_traceSegment_000_1917_0013, g32p_row02_traceSegment_000_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1890 27 27, g32p_row02_traceSegment_000_1890_0027, g32p_row02_traceSegment_000_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1836 54 54, g32p_row02_traceSegment_000_1836_0054, g32p_row02_traceSegment_000_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1728 108 108, g32p_row02_traceSegment_000_1728_0108, g32p_row02_traceSegment_000_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1944 13 14, g32p_row02_traceSegment_000_1944_0013, g32p_row02_traceSegment_000_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1971 13 14, g32p_row02_traceSegment_000_1971_0013, g32p_row02_traceSegment_000_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1944 27 27, g32p_row02_traceSegment_000_1944_0027, g32p_row02_traceSegment_000_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1998 13 14, g32p_row02_traceSegment_000_1998_0013, g32p_row02_traceSegment_000_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2025 13 14, g32p_row02_traceSegment_000_2025_0013, g32p_row02_traceSegment_000_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1998 27 27, g32p_row02_traceSegment_000_1998_0027, g32p_row02_traceSegment_000_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1944 54 54, g32p_row02_traceSegment_000_1944_0054, g32p_row02_traceSegment_000_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2052 13 14, g32p_row02_traceSegment_000_2052_0013, g32p_row02_traceSegment_000_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2079 13 14, g32p_row02_traceSegment_000_2079_0013, g32p_row02_traceSegment_000_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2052 27 27, g32p_row02_traceSegment_000_2052_0027, g32p_row02_traceSegment_000_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2106 13 14, g32p_row02_traceSegment_000_2106_0013, g32p_row02_traceSegment_000_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2133 13 14, g32p_row02_traceSegment_000_2133_0013, g32p_row02_traceSegment_000_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2106 27 27, g32p_row02_traceSegment_000_2106_0027, g32p_row02_traceSegment_000_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2052 54 54, g32p_row02_traceSegment_000_2052_0054, g32p_row02_traceSegment_000_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1944 108 108, g32p_row02_traceSegment_000_1944_0108, g32p_row02_traceSegment_000_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_000 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1728 216 216, g32p_row02_traceSegment_000_1728_0216, g32p_row02_traceSegment_000_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2160 13 14, g32p_row02_traceSegment_000_2160_0013, g32p_row02_traceSegment_000_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2187 13 14, g32p_row02_traceSegment_000_2187_0013, g32p_row02_traceSegment_000_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2160 27 27, g32p_row02_traceSegment_000_2160_0027, g32p_row02_traceSegment_000_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2214 13 14, g32p_row02_traceSegment_000_2214_0013, g32p_row02_traceSegment_000_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2241 13 14, g32p_row02_traceSegment_000_2241_0013, g32p_row02_traceSegment_000_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2214 27 27, g32p_row02_traceSegment_000_2214_0027, g32p_row02_traceSegment_000_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2160 54 54, g32p_row02_traceSegment_000_2160_0054, g32p_row02_traceSegment_000_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2268 13 14, g32p_row02_traceSegment_000_2268_0013, g32p_row02_traceSegment_000_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2295 13 14, g32p_row02_traceSegment_000_2295_0013, g32p_row02_traceSegment_000_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2268 27 27, g32p_row02_traceSegment_000_2268_0027, g32p_row02_traceSegment_000_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2322 13 14, g32p_row02_traceSegment_000_2322_0013, g32p_row02_traceSegment_000_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2349 13 14, g32p_row02_traceSegment_000_2349_0013, g32p_row02_traceSegment_000_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2322 27 27, g32p_row02_traceSegment_000_2322_0027, g32p_row02_traceSegment_000_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2268 54 54, g32p_row02_traceSegment_000_2268_0054, g32p_row02_traceSegment_000_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2160 108 108, g32p_row02_traceSegment_000_2160_0108, g32p_row02_traceSegment_000_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2376 13 14, g32p_row02_traceSegment_000_2376_0013, g32p_row02_traceSegment_000_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2403 13 14, g32p_row02_traceSegment_000_2403_0013, g32p_row02_traceSegment_000_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2376 27 27, g32p_row02_traceSegment_000_2376_0027, g32p_row02_traceSegment_000_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2430 13 14, g32p_row02_traceSegment_000_2430_0013, g32p_row02_traceSegment_000_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2457 13 14, g32p_row02_traceSegment_000_2457_0013, g32p_row02_traceSegment_000_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2430 27 27, g32p_row02_traceSegment_000_2430_0027, g32p_row02_traceSegment_000_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2376 54 54, g32p_row02_traceSegment_000_2376_0054, g32p_row02_traceSegment_000_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2484 13 14, g32p_row02_traceSegment_000_2484_0013, g32p_row02_traceSegment_000_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2511 13 14, g32p_row02_traceSegment_000_2511_0013, g32p_row02_traceSegment_000_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2484 27 27, g32p_row02_traceSegment_000_2484_0027, g32p_row02_traceSegment_000_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2538 13 14, g32p_row02_traceSegment_000_2538_0013, g32p_row02_traceSegment_000_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2565 13 14, g32p_row02_traceSegment_000_2565_0013, g32p_row02_traceSegment_000_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2538 27 27, g32p_row02_traceSegment_000_2538_0027, g32p_row02_traceSegment_000_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2484 54 54, g32p_row02_traceSegment_000_2484_0054, g32p_row02_traceSegment_000_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2376 108 108, g32p_row02_traceSegment_000_2376_0108, g32p_row02_traceSegment_000_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_000 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2160 216 216, g32p_row02_traceSegment_000_2160_0216, g32p_row02_traceSegment_000_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_000 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1728 432 432, g32p_row02_traceSegment_000_1728_0432, g32p_row02_traceSegment_000_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2592 13 14, g32p_row02_traceSegment_000_2592_0013, g32p_row02_traceSegment_000_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2619 13 14, g32p_row02_traceSegment_000_2619_0013, g32p_row02_traceSegment_000_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2592 27 27, g32p_row02_traceSegment_000_2592_0027, g32p_row02_traceSegment_000_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2646 13 14, g32p_row02_traceSegment_000_2646_0013, g32p_row02_traceSegment_000_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2673 13 14, g32p_row02_traceSegment_000_2673_0013, g32p_row02_traceSegment_000_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2646 27 27, g32p_row02_traceSegment_000_2646_0027, g32p_row02_traceSegment_000_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2592 54 54, g32p_row02_traceSegment_000_2592_0054, g32p_row02_traceSegment_000_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2700 13 14, g32p_row02_traceSegment_000_2700_0013, g32p_row02_traceSegment_000_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2727 13 14, g32p_row02_traceSegment_000_2727_0013, g32p_row02_traceSegment_000_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2700 27 27, g32p_row02_traceSegment_000_2700_0027, g32p_row02_traceSegment_000_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2754 13 14, g32p_row02_traceSegment_000_2754_0013, g32p_row02_traceSegment_000_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2781 13 14, g32p_row02_traceSegment_000_2781_0013, g32p_row02_traceSegment_000_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2754 27 27, g32p_row02_traceSegment_000_2754_0027, g32p_row02_traceSegment_000_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2700 54 54, g32p_row02_traceSegment_000_2700_0054, g32p_row02_traceSegment_000_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2592 108 108, g32p_row02_traceSegment_000_2592_0108, g32p_row02_traceSegment_000_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2808 13 14, g32p_row02_traceSegment_000_2808_0013, g32p_row02_traceSegment_000_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2835 13 14, g32p_row02_traceSegment_000_2835_0013, g32p_row02_traceSegment_000_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2808 27 27, g32p_row02_traceSegment_000_2808_0027, g32p_row02_traceSegment_000_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2862 13 14, g32p_row02_traceSegment_000_2862_0013, g32p_row02_traceSegment_000_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2889 13 14, g32p_row02_traceSegment_000_2889_0013, g32p_row02_traceSegment_000_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2862 27 27, g32p_row02_traceSegment_000_2862_0027, g32p_row02_traceSegment_000_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2808 54 54, g32p_row02_traceSegment_000_2808_0054, g32p_row02_traceSegment_000_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2916 13 14, g32p_row02_traceSegment_000_2916_0013, g32p_row02_traceSegment_000_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2943 13 14, g32p_row02_traceSegment_000_2943_0013, g32p_row02_traceSegment_000_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2916 27 27, g32p_row02_traceSegment_000_2916_0027, g32p_row02_traceSegment_000_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2970 13 14, g32p_row02_traceSegment_000_2970_0013, g32p_row02_traceSegment_000_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2997 13 14, g32p_row02_traceSegment_000_2997_0013, g32p_row02_traceSegment_000_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2970 27 27, g32p_row02_traceSegment_000_2970_0027, g32p_row02_traceSegment_000_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2916 54 54, g32p_row02_traceSegment_000_2916_0054, g32p_row02_traceSegment_000_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2808 108 108, g32p_row02_traceSegment_000_2808_0108, g32p_row02_traceSegment_000_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_000 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2592 216 216, g32p_row02_traceSegment_000_2592_0216, g32p_row02_traceSegment_000_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3024 13 14, g32p_row02_traceSegment_000_3024_0013, g32p_row02_traceSegment_000_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3051 13 14, g32p_row02_traceSegment_000_3051_0013, g32p_row02_traceSegment_000_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3024 27 27, g32p_row02_traceSegment_000_3024_0027, g32p_row02_traceSegment_000_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3078 13 14, g32p_row02_traceSegment_000_3078_0013, g32p_row02_traceSegment_000_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3105 13 14, g32p_row02_traceSegment_000_3105_0013, g32p_row02_traceSegment_000_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3078 27 27, g32p_row02_traceSegment_000_3078_0027, g32p_row02_traceSegment_000_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3024 54 54, g32p_row02_traceSegment_000_3024_0054, g32p_row02_traceSegment_000_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3132 13 14, g32p_row02_traceSegment_000_3132_0013, g32p_row02_traceSegment_000_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3159 13 14, g32p_row02_traceSegment_000_3159_0013, g32p_row02_traceSegment_000_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3132 27 27, g32p_row02_traceSegment_000_3132_0027, g32p_row02_traceSegment_000_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3186 13 14, g32p_row02_traceSegment_000_3186_0013, g32p_row02_traceSegment_000_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3213 13 14, g32p_row02_traceSegment_000_3213_0013, g32p_row02_traceSegment_000_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3186 27 27, g32p_row02_traceSegment_000_3186_0027, g32p_row02_traceSegment_000_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3132 54 54, g32p_row02_traceSegment_000_3132_0054, g32p_row02_traceSegment_000_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3024 108 108, g32p_row02_traceSegment_000_3024_0108, g32p_row02_traceSegment_000_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3240 13 14, g32p_row02_traceSegment_000_3240_0013, g32p_row02_traceSegment_000_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3267 13 14, g32p_row02_traceSegment_000_3267_0013, g32p_row02_traceSegment_000_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3240 27 27, g32p_row02_traceSegment_000_3240_0027, g32p_row02_traceSegment_000_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3294 13 14, g32p_row02_traceSegment_000_3294_0013, g32p_row02_traceSegment_000_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3321 13 14, g32p_row02_traceSegment_000_3321_0013, g32p_row02_traceSegment_000_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3294 27 27, g32p_row02_traceSegment_000_3294_0027, g32p_row02_traceSegment_000_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3240 54 54, g32p_row02_traceSegment_000_3240_0054, g32p_row02_traceSegment_000_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3348 13 14, g32p_row02_traceSegment_000_3348_0013, g32p_row02_traceSegment_000_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3375 13 14, g32p_row02_traceSegment_000_3375_0013, g32p_row02_traceSegment_000_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3348 27 27, g32p_row02_traceSegment_000_3348_0027, g32p_row02_traceSegment_000_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3402 13 14, g32p_row02_traceSegment_000_3402_0013, g32p_row02_traceSegment_000_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_000 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_000 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_000_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_000 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3429 13 14, g32p_row02_traceSegment_000_3429_0013, g32p_row02_traceSegment_000_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_000 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3402 27 27, g32p_row02_traceSegment_000_3402_0027, g32p_row02_traceSegment_000_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_000 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3348 54 54, g32p_row02_traceSegment_000_3348_0054, g32p_row02_traceSegment_000_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_000 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3240 108 108, g32p_row02_traceSegment_000_3240_0108, g32p_row02_traceSegment_000_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_000_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_000 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 3024 216 216, g32p_row02_traceSegment_000_3024_0216, g32p_row02_traceSegment_000_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_000_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_000 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 2592 432 432, g32p_row02_traceSegment_000_2592_0432, g32p_row02_traceSegment_000_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_000_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_000 1728 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 1728 864 864, g32p_row02_traceSegment_000_1728_0864, g32p_row02_traceSegment_000_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_000_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_000 0 3456 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_000 0 1728 1728, g32p_row02_traceSegment_000_0000_1728, g32p_row02_traceSegment_000_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 0 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_000_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_001 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 1 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_001_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 0 13 14, g32p_row02_traceSegment_001_0000_0013, g32p_row02_traceSegment_001_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 27 13 14, g32p_row02_traceSegment_001_0027_0013, g32p_row02_traceSegment_001_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 0 27 27, g32p_row02_traceSegment_001_0000_0027, g32p_row02_traceSegment_001_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 54 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 54 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 54 13 14, g32p_row02_traceSegment_001_0054_0013, g32p_row02_traceSegment_001_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 81 13 14, g32p_row02_traceSegment_001_0081_0013, g32p_row02_traceSegment_001_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 54 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 54 27 27, g32p_row02_traceSegment_001_0054_0027, g32p_row02_traceSegment_001_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 0 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 0 54 54, g32p_row02_traceSegment_001_0000_0054, g32p_row02_traceSegment_001_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 108 13 14, g32p_row02_traceSegment_001_0108_0013, g32p_row02_traceSegment_001_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 135 13 14, g32p_row02_traceSegment_001_0135_0013, g32p_row02_traceSegment_001_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 108 27 27, g32p_row02_traceSegment_001_0108_0027, g32p_row02_traceSegment_001_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 162 13 14, g32p_row02_traceSegment_001_0162_0013, g32p_row02_traceSegment_001_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 189 13 14, g32p_row02_traceSegment_001_0189_0013, g32p_row02_traceSegment_001_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 162 27 27, g32p_row02_traceSegment_001_0162_0027, g32p_row02_traceSegment_001_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 108 54 54, g32p_row02_traceSegment_001_0108_0054, g32p_row02_traceSegment_001_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 0 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 0 108 108, g32p_row02_traceSegment_001_0000_0108, g32p_row02_traceSegment_001_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 216 13 14, g32p_row02_traceSegment_001_0216_0013, g32p_row02_traceSegment_001_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 243 13 14, g32p_row02_traceSegment_001_0243_0013, g32p_row02_traceSegment_001_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 216 27 27, g32p_row02_traceSegment_001_0216_0027, g32p_row02_traceSegment_001_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 270 13 14, g32p_row02_traceSegment_001_0270_0013, g32p_row02_traceSegment_001_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 297 13 14, g32p_row02_traceSegment_001_0297_0013, g32p_row02_traceSegment_001_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 270 27 27, g32p_row02_traceSegment_001_0270_0027, g32p_row02_traceSegment_001_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 216 54 54, g32p_row02_traceSegment_001_0216_0054, g32p_row02_traceSegment_001_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 324 13 14, g32p_row02_traceSegment_001_0324_0013, g32p_row02_traceSegment_001_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 364 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 351 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 351 13 14, g32p_row02_traceSegment_001_0351_0013, g32p_row02_traceSegment_001_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 324 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 324 27 27, g32p_row02_traceSegment_001_0324_0027, g32p_row02_traceSegment_001_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 378 13 14, g32p_row02_traceSegment_001_0378_0013, g32p_row02_traceSegment_001_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 405 13 14, g32p_row02_traceSegment_001_0405_0013, g32p_row02_traceSegment_001_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 378 27 27, g32p_row02_traceSegment_001_0378_0027, g32p_row02_traceSegment_001_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 324 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 324 54 54, g32p_row02_traceSegment_001_0324_0054, g32p_row02_traceSegment_001_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 216 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 216 108 108, g32p_row02_traceSegment_001_0216_0108, g32p_row02_traceSegment_001_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_001 0 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 0 216 216, g32p_row02_traceSegment_001_0000_0216, g32p_row02_traceSegment_001_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 432 13 14, g32p_row02_traceSegment_001_0432_0013, g32p_row02_traceSegment_001_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 459 13 14, g32p_row02_traceSegment_001_0459_0013, g32p_row02_traceSegment_001_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 432 27 27, g32p_row02_traceSegment_001_0432_0027, g32p_row02_traceSegment_001_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 486 13 14, g32p_row02_traceSegment_001_0486_0013, g32p_row02_traceSegment_001_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 513 13 14, g32p_row02_traceSegment_001_0513_0013, g32p_row02_traceSegment_001_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 486 27 27, g32p_row02_traceSegment_001_0486_0027, g32p_row02_traceSegment_001_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 432 54 54, g32p_row02_traceSegment_001_0432_0054, g32p_row02_traceSegment_001_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 540 13 14, g32p_row02_traceSegment_001_0540_0013, g32p_row02_traceSegment_001_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 567 13 14, g32p_row02_traceSegment_001_0567_0013, g32p_row02_traceSegment_001_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 540 27 27, g32p_row02_traceSegment_001_0540_0027, g32p_row02_traceSegment_001_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 594 13 14, g32p_row02_traceSegment_001_0594_0013, g32p_row02_traceSegment_001_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 621 13 14, g32p_row02_traceSegment_001_0621_0013, g32p_row02_traceSegment_001_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 594 27 27, g32p_row02_traceSegment_001_0594_0027, g32p_row02_traceSegment_001_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 540 54 54, g32p_row02_traceSegment_001_0540_0054, g32p_row02_traceSegment_001_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 432 108 108, g32p_row02_traceSegment_001_0432_0108, g32p_row02_traceSegment_001_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 648 13 14, g32p_row02_traceSegment_001_0648_0013, g32p_row02_traceSegment_001_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 675 13 14, g32p_row02_traceSegment_001_0675_0013, g32p_row02_traceSegment_001_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 648 27 27, g32p_row02_traceSegment_001_0648_0027, g32p_row02_traceSegment_001_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 702 13 14, g32p_row02_traceSegment_001_0702_0013, g32p_row02_traceSegment_001_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 729 13 14, g32p_row02_traceSegment_001_0729_0013, g32p_row02_traceSegment_001_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 702 27 27, g32p_row02_traceSegment_001_0702_0027, g32p_row02_traceSegment_001_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 648 54 54, g32p_row02_traceSegment_001_0648_0054, g32p_row02_traceSegment_001_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 756 13 14, g32p_row02_traceSegment_001_0756_0013, g32p_row02_traceSegment_001_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 783 13 14, g32p_row02_traceSegment_001_0783_0013, g32p_row02_traceSegment_001_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 756 27 27, g32p_row02_traceSegment_001_0756_0027, g32p_row02_traceSegment_001_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 810 13 14, g32p_row02_traceSegment_001_0810_0013, g32p_row02_traceSegment_001_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 837 13 14, g32p_row02_traceSegment_001_0837_0013, g32p_row02_traceSegment_001_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 810 27 27, g32p_row02_traceSegment_001_0810_0027, g32p_row02_traceSegment_001_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 756 54 54, g32p_row02_traceSegment_001_0756_0054, g32p_row02_traceSegment_001_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 648 108 108, g32p_row02_traceSegment_001_0648_0108, g32p_row02_traceSegment_001_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_001 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 432 216 216, g32p_row02_traceSegment_001_0432_0216, g32p_row02_traceSegment_001_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_001 0 864 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 0 432 432, g32p_row02_traceSegment_001_0000_0432, g32p_row02_traceSegment_001_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 864 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 864 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 864 13 14, g32p_row02_traceSegment_001_0864_0013, g32p_row02_traceSegment_001_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 891 13 14, g32p_row02_traceSegment_001_0891_0013, g32p_row02_traceSegment_001_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 864 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 864 27 27, g32p_row02_traceSegment_001_0864_0027, g32p_row02_traceSegment_001_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 918 13 14, g32p_row02_traceSegment_001_0918_0013, g32p_row02_traceSegment_001_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 945 13 14, g32p_row02_traceSegment_001_0945_0013, g32p_row02_traceSegment_001_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 918 27 27, g32p_row02_traceSegment_001_0918_0027, g32p_row02_traceSegment_001_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 864 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 864 54 54, g32p_row02_traceSegment_001_0864_0054, g32p_row02_traceSegment_001_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 972 13 14, g32p_row02_traceSegment_001_0972_0013, g32p_row02_traceSegment_001_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 999 13 14, g32p_row02_traceSegment_001_0999_0013, g32p_row02_traceSegment_001_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 972 27 27, g32p_row02_traceSegment_001_0972_0027, g32p_row02_traceSegment_001_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1026 13 14, g32p_row02_traceSegment_001_1026_0013, g32p_row02_traceSegment_001_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1053 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1053 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1053 13 14, g32p_row02_traceSegment_001_1053_0013, g32p_row02_traceSegment_001_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1026 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1026 27 27, g32p_row02_traceSegment_001_1026_0027, g32p_row02_traceSegment_001_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 972 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 972 54 54, g32p_row02_traceSegment_001_0972_0054, g32p_row02_traceSegment_001_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 864 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 864 108 108, g32p_row02_traceSegment_001_0864_0108, g32p_row02_traceSegment_001_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1080 13 14, g32p_row02_traceSegment_001_1080_0013, g32p_row02_traceSegment_001_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1107 13 14, g32p_row02_traceSegment_001_1107_0013, g32p_row02_traceSegment_001_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1080 27 27, g32p_row02_traceSegment_001_1080_0027, g32p_row02_traceSegment_001_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1134 13 14, g32p_row02_traceSegment_001_1134_0013, g32p_row02_traceSegment_001_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1161 13 14, g32p_row02_traceSegment_001_1161_0013, g32p_row02_traceSegment_001_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1134 27 27, g32p_row02_traceSegment_001_1134_0027, g32p_row02_traceSegment_001_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1080 54 54, g32p_row02_traceSegment_001_1080_0054, g32p_row02_traceSegment_001_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1188 13 14, g32p_row02_traceSegment_001_1188_0013, g32p_row02_traceSegment_001_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1215 13 14, g32p_row02_traceSegment_001_1215_0013, g32p_row02_traceSegment_001_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1188 27 27, g32p_row02_traceSegment_001_1188_0027, g32p_row02_traceSegment_001_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1242 13 14, g32p_row02_traceSegment_001_1242_0013, g32p_row02_traceSegment_001_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1269 13 14, g32p_row02_traceSegment_001_1269_0013, g32p_row02_traceSegment_001_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1242 27 27, g32p_row02_traceSegment_001_1242_0027, g32p_row02_traceSegment_001_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1188 54 54, g32p_row02_traceSegment_001_1188_0054, g32p_row02_traceSegment_001_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1080 108 108, g32p_row02_traceSegment_001_1080_0108, g32p_row02_traceSegment_001_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_001 864 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 864 216 216, g32p_row02_traceSegment_001_0864_0216, g32p_row02_traceSegment_001_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1296 13 14, g32p_row02_traceSegment_001_1296_0013, g32p_row02_traceSegment_001_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1323 13 14, g32p_row02_traceSegment_001_1323_0013, g32p_row02_traceSegment_001_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1296 27 27, g32p_row02_traceSegment_001_1296_0027, g32p_row02_traceSegment_001_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1350 13 14, g32p_row02_traceSegment_001_1350_0013, g32p_row02_traceSegment_001_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1377 13 14, g32p_row02_traceSegment_001_1377_0013, g32p_row02_traceSegment_001_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1350 27 27, g32p_row02_traceSegment_001_1350_0027, g32p_row02_traceSegment_001_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1296 54 54, g32p_row02_traceSegment_001_1296_0054, g32p_row02_traceSegment_001_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1404 13 14, g32p_row02_traceSegment_001_1404_0013, g32p_row02_traceSegment_001_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1431 13 14, g32p_row02_traceSegment_001_1431_0013, g32p_row02_traceSegment_001_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1404 27 27, g32p_row02_traceSegment_001_1404_0027, g32p_row02_traceSegment_001_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1458 13 14, g32p_row02_traceSegment_001_1458_0013, g32p_row02_traceSegment_001_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1485 13 14, g32p_row02_traceSegment_001_1485_0013, g32p_row02_traceSegment_001_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1458 27 27, g32p_row02_traceSegment_001_1458_0027, g32p_row02_traceSegment_001_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1404 54 54, g32p_row02_traceSegment_001_1404_0054, g32p_row02_traceSegment_001_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1296 108 108, g32p_row02_traceSegment_001_1296_0108, g32p_row02_traceSegment_001_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1512 13 14, g32p_row02_traceSegment_001_1512_0013, g32p_row02_traceSegment_001_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1539 13 14, g32p_row02_traceSegment_001_1539_0013, g32p_row02_traceSegment_001_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1512 27 27, g32p_row02_traceSegment_001_1512_0027, g32p_row02_traceSegment_001_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1566 13 14, g32p_row02_traceSegment_001_1566_0013, g32p_row02_traceSegment_001_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1593 13 14, g32p_row02_traceSegment_001_1593_0013, g32p_row02_traceSegment_001_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1566 27 27, g32p_row02_traceSegment_001_1566_0027, g32p_row02_traceSegment_001_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1512 54 54, g32p_row02_traceSegment_001_1512_0054, g32p_row02_traceSegment_001_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1620 13 14, g32p_row02_traceSegment_001_1620_0013, g32p_row02_traceSegment_001_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1647 13 14, g32p_row02_traceSegment_001_1647_0013, g32p_row02_traceSegment_001_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1620 27 27, g32p_row02_traceSegment_001_1620_0027, g32p_row02_traceSegment_001_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1674 13 14, g32p_row02_traceSegment_001_1674_0013, g32p_row02_traceSegment_001_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1701 13 14, g32p_row02_traceSegment_001_1701_0013, g32p_row02_traceSegment_001_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1674 27 27, g32p_row02_traceSegment_001_1674_0027, g32p_row02_traceSegment_001_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1620 54 54, g32p_row02_traceSegment_001_1620_0054, g32p_row02_traceSegment_001_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1512 108 108, g32p_row02_traceSegment_001_1512_0108, g32p_row02_traceSegment_001_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_001 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1296 216 216, g32p_row02_traceSegment_001_1296_0216, g32p_row02_traceSegment_001_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_001 864 864 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 864 432 432, g32p_row02_traceSegment_001_0864_0432, g32p_row02_traceSegment_001_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_001 0 1728 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 0 864 864, g32p_row02_traceSegment_001_0000_0864, g32p_row02_traceSegment_001_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1728 13 14, g32p_row02_traceSegment_001_1728_0013, g32p_row02_traceSegment_001_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1755 13 14, g32p_row02_traceSegment_001_1755_0013, g32p_row02_traceSegment_001_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1728 27 27, g32p_row02_traceSegment_001_1728_0027, g32p_row02_traceSegment_001_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1782 13 14, g32p_row02_traceSegment_001_1782_0013, g32p_row02_traceSegment_001_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1809 13 14, g32p_row02_traceSegment_001_1809_0013, g32p_row02_traceSegment_001_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1782 27 27, g32p_row02_traceSegment_001_1782_0027, g32p_row02_traceSegment_001_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1728 54 54, g32p_row02_traceSegment_001_1728_0054, g32p_row02_traceSegment_001_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1836 13 14, g32p_row02_traceSegment_001_1836_0013, g32p_row02_traceSegment_001_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1863 13 14, g32p_row02_traceSegment_001_1863_0013, g32p_row02_traceSegment_001_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1836 27 27, g32p_row02_traceSegment_001_1836_0027, g32p_row02_traceSegment_001_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1890 13 14, g32p_row02_traceSegment_001_1890_0013, g32p_row02_traceSegment_001_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1917 13 14, g32p_row02_traceSegment_001_1917_0013, g32p_row02_traceSegment_001_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1890 27 27, g32p_row02_traceSegment_001_1890_0027, g32p_row02_traceSegment_001_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1836 54 54, g32p_row02_traceSegment_001_1836_0054, g32p_row02_traceSegment_001_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1728 108 108, g32p_row02_traceSegment_001_1728_0108, g32p_row02_traceSegment_001_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1944 13 14, g32p_row02_traceSegment_001_1944_0013, g32p_row02_traceSegment_001_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1971 13 14, g32p_row02_traceSegment_001_1971_0013, g32p_row02_traceSegment_001_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1944 27 27, g32p_row02_traceSegment_001_1944_0027, g32p_row02_traceSegment_001_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1998 13 14, g32p_row02_traceSegment_001_1998_0013, g32p_row02_traceSegment_001_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2025 13 14, g32p_row02_traceSegment_001_2025_0013, g32p_row02_traceSegment_001_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1998 27 27, g32p_row02_traceSegment_001_1998_0027, g32p_row02_traceSegment_001_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1944 54 54, g32p_row02_traceSegment_001_1944_0054, g32p_row02_traceSegment_001_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2052 13 14, g32p_row02_traceSegment_001_2052_0013, g32p_row02_traceSegment_001_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2079 13 14, g32p_row02_traceSegment_001_2079_0013, g32p_row02_traceSegment_001_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2052 27 27, g32p_row02_traceSegment_001_2052_0027, g32p_row02_traceSegment_001_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2106 13 14, g32p_row02_traceSegment_001_2106_0013, g32p_row02_traceSegment_001_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2133 13 14, g32p_row02_traceSegment_001_2133_0013, g32p_row02_traceSegment_001_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2106 27 27, g32p_row02_traceSegment_001_2106_0027, g32p_row02_traceSegment_001_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2052 54 54, g32p_row02_traceSegment_001_2052_0054, g32p_row02_traceSegment_001_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1944 108 108, g32p_row02_traceSegment_001_1944_0108, g32p_row02_traceSegment_001_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_001 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1728 216 216, g32p_row02_traceSegment_001_1728_0216, g32p_row02_traceSegment_001_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2160 13 14, g32p_row02_traceSegment_001_2160_0013, g32p_row02_traceSegment_001_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2187 13 14, g32p_row02_traceSegment_001_2187_0013, g32p_row02_traceSegment_001_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2160 27 27, g32p_row02_traceSegment_001_2160_0027, g32p_row02_traceSegment_001_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2214 13 14, g32p_row02_traceSegment_001_2214_0013, g32p_row02_traceSegment_001_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2241 13 14, g32p_row02_traceSegment_001_2241_0013, g32p_row02_traceSegment_001_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2214 27 27, g32p_row02_traceSegment_001_2214_0027, g32p_row02_traceSegment_001_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2160 54 54, g32p_row02_traceSegment_001_2160_0054, g32p_row02_traceSegment_001_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2268 13 14, g32p_row02_traceSegment_001_2268_0013, g32p_row02_traceSegment_001_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2295 13 14, g32p_row02_traceSegment_001_2295_0013, g32p_row02_traceSegment_001_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2268 27 27, g32p_row02_traceSegment_001_2268_0027, g32p_row02_traceSegment_001_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2322 13 14, g32p_row02_traceSegment_001_2322_0013, g32p_row02_traceSegment_001_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2349 13 14, g32p_row02_traceSegment_001_2349_0013, g32p_row02_traceSegment_001_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2322 27 27, g32p_row02_traceSegment_001_2322_0027, g32p_row02_traceSegment_001_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2268 54 54, g32p_row02_traceSegment_001_2268_0054, g32p_row02_traceSegment_001_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2160 108 108, g32p_row02_traceSegment_001_2160_0108, g32p_row02_traceSegment_001_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2376 13 14, g32p_row02_traceSegment_001_2376_0013, g32p_row02_traceSegment_001_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2403 13 14, g32p_row02_traceSegment_001_2403_0013, g32p_row02_traceSegment_001_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2376 27 27, g32p_row02_traceSegment_001_2376_0027, g32p_row02_traceSegment_001_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2430 13 14, g32p_row02_traceSegment_001_2430_0013, g32p_row02_traceSegment_001_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2457 13 14, g32p_row02_traceSegment_001_2457_0013, g32p_row02_traceSegment_001_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2430 27 27, g32p_row02_traceSegment_001_2430_0027, g32p_row02_traceSegment_001_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2376 54 54, g32p_row02_traceSegment_001_2376_0054, g32p_row02_traceSegment_001_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2484 13 14, g32p_row02_traceSegment_001_2484_0013, g32p_row02_traceSegment_001_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2511 13 14, g32p_row02_traceSegment_001_2511_0013, g32p_row02_traceSegment_001_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2484 27 27, g32p_row02_traceSegment_001_2484_0027, g32p_row02_traceSegment_001_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2538 13 14, g32p_row02_traceSegment_001_2538_0013, g32p_row02_traceSegment_001_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2565 13 14, g32p_row02_traceSegment_001_2565_0013, g32p_row02_traceSegment_001_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2538 27 27, g32p_row02_traceSegment_001_2538_0027, g32p_row02_traceSegment_001_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2484 54 54, g32p_row02_traceSegment_001_2484_0054, g32p_row02_traceSegment_001_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2376 108 108, g32p_row02_traceSegment_001_2376_0108, g32p_row02_traceSegment_001_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_001 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2160 216 216, g32p_row02_traceSegment_001_2160_0216, g32p_row02_traceSegment_001_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_001 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1728 432 432, g32p_row02_traceSegment_001_1728_0432, g32p_row02_traceSegment_001_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2592 13 14, g32p_row02_traceSegment_001_2592_0013, g32p_row02_traceSegment_001_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2619 13 14, g32p_row02_traceSegment_001_2619_0013, g32p_row02_traceSegment_001_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2592 27 27, g32p_row02_traceSegment_001_2592_0027, g32p_row02_traceSegment_001_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2646 13 14, g32p_row02_traceSegment_001_2646_0013, g32p_row02_traceSegment_001_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2673 13 14, g32p_row02_traceSegment_001_2673_0013, g32p_row02_traceSegment_001_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2646 27 27, g32p_row02_traceSegment_001_2646_0027, g32p_row02_traceSegment_001_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2592 54 54, g32p_row02_traceSegment_001_2592_0054, g32p_row02_traceSegment_001_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2700 13 14, g32p_row02_traceSegment_001_2700_0013, g32p_row02_traceSegment_001_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2727 13 14, g32p_row02_traceSegment_001_2727_0013, g32p_row02_traceSegment_001_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2700 27 27, g32p_row02_traceSegment_001_2700_0027, g32p_row02_traceSegment_001_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2767 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2754 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2754 13 14, g32p_row02_traceSegment_001_2754_0013, g32p_row02_traceSegment_001_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2781 13 14, g32p_row02_traceSegment_001_2781_0013, g32p_row02_traceSegment_001_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2754 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2754 27 27, g32p_row02_traceSegment_001_2754_0027, g32p_row02_traceSegment_001_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 2700 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2700 54 54, g32p_row02_traceSegment_001_2700_0054, g32p_row02_traceSegment_001_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 2592 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2592 108 108, g32p_row02_traceSegment_001_2592_0108, g32p_row02_traceSegment_001_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2808 13 14, g32p_row02_traceSegment_001_2808_0013, g32p_row02_traceSegment_001_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2835 13 14, g32p_row02_traceSegment_001_2835_0013, g32p_row02_traceSegment_001_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2808 27 27, g32p_row02_traceSegment_001_2808_0027, g32p_row02_traceSegment_001_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2862 13 14, g32p_row02_traceSegment_001_2862_0013, g32p_row02_traceSegment_001_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2889 13 14, g32p_row02_traceSegment_001_2889_0013, g32p_row02_traceSegment_001_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2862 27 27, g32p_row02_traceSegment_001_2862_0027, g32p_row02_traceSegment_001_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2808 54 54, g32p_row02_traceSegment_001_2808_0054, g32p_row02_traceSegment_001_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2916 13 14, g32p_row02_traceSegment_001_2916_0013, g32p_row02_traceSegment_001_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2943 13 14, g32p_row02_traceSegment_001_2943_0013, g32p_row02_traceSegment_001_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2916 27 27, g32p_row02_traceSegment_001_2916_0027, g32p_row02_traceSegment_001_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2970 13 14, g32p_row02_traceSegment_001_2970_0013, g32p_row02_traceSegment_001_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2997 13 14, g32p_row02_traceSegment_001_2997_0013, g32p_row02_traceSegment_001_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2970 27 27, g32p_row02_traceSegment_001_2970_0027, g32p_row02_traceSegment_001_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2916 54 54, g32p_row02_traceSegment_001_2916_0054, g32p_row02_traceSegment_001_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2808 108 108, g32p_row02_traceSegment_001_2808_0108, g32p_row02_traceSegment_001_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_001 2592 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2592 216 216, g32p_row02_traceSegment_001_2592_0216, g32p_row02_traceSegment_001_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3024 13 14, g32p_row02_traceSegment_001_3024_0013, g32p_row02_traceSegment_001_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3051 13 14, g32p_row02_traceSegment_001_3051_0013, g32p_row02_traceSegment_001_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3024 27 27, g32p_row02_traceSegment_001_3024_0027, g32p_row02_traceSegment_001_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3078 13 14, g32p_row02_traceSegment_001_3078_0013, g32p_row02_traceSegment_001_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3105 13 14, g32p_row02_traceSegment_001_3105_0013, g32p_row02_traceSegment_001_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3078 27 27, g32p_row02_traceSegment_001_3078_0027, g32p_row02_traceSegment_001_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3024 54 54, g32p_row02_traceSegment_001_3024_0054, g32p_row02_traceSegment_001_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3132 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3132 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3132 13 14, g32p_row02_traceSegment_001_3132_0013, g32p_row02_traceSegment_001_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3159 13 14, g32p_row02_traceSegment_001_3159_0013, g32p_row02_traceSegment_001_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 3132 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3132 27 27, g32p_row02_traceSegment_001_3132_0027, g32p_row02_traceSegment_001_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3186 13 14, g32p_row02_traceSegment_001_3186_0013, g32p_row02_traceSegment_001_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3213 13 14, g32p_row02_traceSegment_001_3213_0013, g32p_row02_traceSegment_001_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3186 27 27, g32p_row02_traceSegment_001_3186_0027, g32p_row02_traceSegment_001_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 3132 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3132 54 54, g32p_row02_traceSegment_001_3132_0054, g32p_row02_traceSegment_001_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 3024 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3024 108 108, g32p_row02_traceSegment_001_3024_0108, g32p_row02_traceSegment_001_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3240 13 14, g32p_row02_traceSegment_001_3240_0013, g32p_row02_traceSegment_001_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3267 13 14, g32p_row02_traceSegment_001_3267_0013, g32p_row02_traceSegment_001_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3240 27 27, g32p_row02_traceSegment_001_3240_0027, g32p_row02_traceSegment_001_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3294 13 14, g32p_row02_traceSegment_001_3294_0013, g32p_row02_traceSegment_001_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3321 13 14, g32p_row02_traceSegment_001_3321_0013, g32p_row02_traceSegment_001_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3294 27 27, g32p_row02_traceSegment_001_3294_0027, g32p_row02_traceSegment_001_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3240 54 54, g32p_row02_traceSegment_001_3240_0054, g32p_row02_traceSegment_001_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3348 13 14, g32p_row02_traceSegment_001_3348_0013, g32p_row02_traceSegment_001_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3375 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3388 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3375 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3375 13 14, g32p_row02_traceSegment_001_3375_0013, g32p_row02_traceSegment_001_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 3348 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3348 27 27, g32p_row02_traceSegment_001_3348_0027, g32p_row02_traceSegment_001_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3402 13 14, g32p_row02_traceSegment_001_3402_0013, g32p_row02_traceSegment_001_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_001 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_001 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_001_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_001 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3429 13 14, g32p_row02_traceSegment_001_3429_0013, g32p_row02_traceSegment_001_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_001 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3402 27 27, g32p_row02_traceSegment_001_3402_0027, g32p_row02_traceSegment_001_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_001 3348 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3348 54 54, g32p_row02_traceSegment_001_3348_0054, g32p_row02_traceSegment_001_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_001 3240 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3240 108 108, g32p_row02_traceSegment_001_3240_0108, g32p_row02_traceSegment_001_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_001_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_001 3024 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 3024 216 216, g32p_row02_traceSegment_001_3024_0216, g32p_row02_traceSegment_001_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_001_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_001 2592 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 2592 432 432, g32p_row02_traceSegment_001_2592_0432, g32p_row02_traceSegment_001_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_001_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_001 1728 1728 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 1728 864 864, g32p_row02_traceSegment_001_1728_0864, g32p_row02_traceSegment_001_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_001_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_001 0 3456 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_001 0 1728 1728, g32p_row02_traceSegment_001_0000_1728, g32p_row02_traceSegment_001_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 1 = [8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_001_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_002 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 2 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_002_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 0 13 14, g32p_row02_traceSegment_002_0000_0013, g32p_row02_traceSegment_002_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 40 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 27 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 27 13 14, g32p_row02_traceSegment_002_0027_0013, g32p_row02_traceSegment_002_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 0 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 0 27 27, g32p_row02_traceSegment_002_0000_0027, g32p_row02_traceSegment_002_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 54 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 54 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 54 13 14, g32p_row02_traceSegment_002_0054_0013, g32p_row02_traceSegment_002_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 81 13 14, g32p_row02_traceSegment_002_0081_0013, g32p_row02_traceSegment_002_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 54 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 54 27 27, g32p_row02_traceSegment_002_0054_0027, g32p_row02_traceSegment_002_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 0 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 0 54 54, g32p_row02_traceSegment_002_0000_0054, g32p_row02_traceSegment_002_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 108 13 14, g32p_row02_traceSegment_002_0108_0013, g32p_row02_traceSegment_002_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 135 13 14, g32p_row02_traceSegment_002_0135_0013, g32p_row02_traceSegment_002_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 108 27 27, g32p_row02_traceSegment_002_0108_0027, g32p_row02_traceSegment_002_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 162 13 14, g32p_row02_traceSegment_002_0162_0013, g32p_row02_traceSegment_002_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 189 13 14, g32p_row02_traceSegment_002_0189_0013, g32p_row02_traceSegment_002_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 162 27 27, g32p_row02_traceSegment_002_0162_0027, g32p_row02_traceSegment_002_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 108 54 54, g32p_row02_traceSegment_002_0108_0054, g32p_row02_traceSegment_002_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 0 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 0 108 108, g32p_row02_traceSegment_002_0000_0108, g32p_row02_traceSegment_002_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 216 13 14, g32p_row02_traceSegment_002_0216_0013, g32p_row02_traceSegment_002_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 243 13 14, g32p_row02_traceSegment_002_0243_0013, g32p_row02_traceSegment_002_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 216 27 27, g32p_row02_traceSegment_002_0216_0027, g32p_row02_traceSegment_002_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 270 13 14, g32p_row02_traceSegment_002_0270_0013, g32p_row02_traceSegment_002_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 297 13 14, g32p_row02_traceSegment_002_0297_0013, g32p_row02_traceSegment_002_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 270 27 27, g32p_row02_traceSegment_002_0270_0027, g32p_row02_traceSegment_002_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 216 54 54, g32p_row02_traceSegment_002_0216_0054, g32p_row02_traceSegment_002_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 324 13 14, g32p_row02_traceSegment_002_0324_0013, g32p_row02_traceSegment_002_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 351 13 14, g32p_row02_traceSegment_002_0351_0013, g32p_row02_traceSegment_002_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 324 27 27, g32p_row02_traceSegment_002_0324_0027, g32p_row02_traceSegment_002_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 378 13 14, g32p_row02_traceSegment_002_0378_0013, g32p_row02_traceSegment_002_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 405 13 14, g32p_row02_traceSegment_002_0405_0013, g32p_row02_traceSegment_002_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 378 27 27, g32p_row02_traceSegment_002_0378_0027, g32p_row02_traceSegment_002_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 324 54 54, g32p_row02_traceSegment_002_0324_0054, g32p_row02_traceSegment_002_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 216 108 108, g32p_row02_traceSegment_002_0216_0108, g32p_row02_traceSegment_002_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_002 0 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 0 216 216, g32p_row02_traceSegment_002_0000_0216, g32p_row02_traceSegment_002_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 432 13 14, g32p_row02_traceSegment_002_0432_0013, g32p_row02_traceSegment_002_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 459 13 14, g32p_row02_traceSegment_002_0459_0013, g32p_row02_traceSegment_002_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 432 27 27, g32p_row02_traceSegment_002_0432_0027, g32p_row02_traceSegment_002_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 486 13 14, g32p_row02_traceSegment_002_0486_0013, g32p_row02_traceSegment_002_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 513 13 14, g32p_row02_traceSegment_002_0513_0013, g32p_row02_traceSegment_002_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 486 27 27, g32p_row02_traceSegment_002_0486_0027, g32p_row02_traceSegment_002_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 432 54 54, g32p_row02_traceSegment_002_0432_0054, g32p_row02_traceSegment_002_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 540 13 14, g32p_row02_traceSegment_002_0540_0013, g32p_row02_traceSegment_002_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 567 13 14, g32p_row02_traceSegment_002_0567_0013, g32p_row02_traceSegment_002_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 540 27 27, g32p_row02_traceSegment_002_0540_0027, g32p_row02_traceSegment_002_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 594 13 14, g32p_row02_traceSegment_002_0594_0013, g32p_row02_traceSegment_002_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 621 13 14, g32p_row02_traceSegment_002_0621_0013, g32p_row02_traceSegment_002_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 594 27 27, g32p_row02_traceSegment_002_0594_0027, g32p_row02_traceSegment_002_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 540 54 54, g32p_row02_traceSegment_002_0540_0054, g32p_row02_traceSegment_002_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 432 108 108, g32p_row02_traceSegment_002_0432_0108, g32p_row02_traceSegment_002_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 648 13 14, g32p_row02_traceSegment_002_0648_0013, g32p_row02_traceSegment_002_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 675 13 14, g32p_row02_traceSegment_002_0675_0013, g32p_row02_traceSegment_002_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 648 27 27, g32p_row02_traceSegment_002_0648_0027, g32p_row02_traceSegment_002_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 702 13 14, g32p_row02_traceSegment_002_0702_0013, g32p_row02_traceSegment_002_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 729 13 14, g32p_row02_traceSegment_002_0729_0013, g32p_row02_traceSegment_002_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 702 27 27, g32p_row02_traceSegment_002_0702_0027, g32p_row02_traceSegment_002_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 648 54 54, g32p_row02_traceSegment_002_0648_0054, g32p_row02_traceSegment_002_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 756 13 14, g32p_row02_traceSegment_002_0756_0013, g32p_row02_traceSegment_002_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 783 13 14, g32p_row02_traceSegment_002_0783_0013, g32p_row02_traceSegment_002_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 756 27 27, g32p_row02_traceSegment_002_0756_0027, g32p_row02_traceSegment_002_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 810 13 14, g32p_row02_traceSegment_002_0810_0013, g32p_row02_traceSegment_002_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 850 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 837 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 837 13 14, g32p_row02_traceSegment_002_0837_0013, g32p_row02_traceSegment_002_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 810 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 810 27 27, g32p_row02_traceSegment_002_0810_0027, g32p_row02_traceSegment_002_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 756 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 756 54 54, g32p_row02_traceSegment_002_0756_0054, g32p_row02_traceSegment_002_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 648 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 648 108 108, g32p_row02_traceSegment_002_0648_0108, g32p_row02_traceSegment_002_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_002 432 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 432 216 216, g32p_row02_traceSegment_002_0432_0216, g32p_row02_traceSegment_002_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_002 0 864 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 0 432 432, g32p_row02_traceSegment_002_0000_0432, g32p_row02_traceSegment_002_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 864 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 864 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 864 13 14, g32p_row02_traceSegment_002_0864_0013, g32p_row02_traceSegment_002_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 891 13 14, g32p_row02_traceSegment_002_0891_0013, g32p_row02_traceSegment_002_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 864 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 864 27 27, g32p_row02_traceSegment_002_0864_0027, g32p_row02_traceSegment_002_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 918 13 14, g32p_row02_traceSegment_002_0918_0013, g32p_row02_traceSegment_002_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 945 13 14, g32p_row02_traceSegment_002_0945_0013, g32p_row02_traceSegment_002_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 918 27 27, g32p_row02_traceSegment_002_0918_0027, g32p_row02_traceSegment_002_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 864 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 864 54 54, g32p_row02_traceSegment_002_0864_0054, g32p_row02_traceSegment_002_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 972 13 14, g32p_row02_traceSegment_002_0972_0013, g32p_row02_traceSegment_002_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 999 13 14, g32p_row02_traceSegment_002_0999_0013, g32p_row02_traceSegment_002_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 972 27 27, g32p_row02_traceSegment_002_0972_0027, g32p_row02_traceSegment_002_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1026 13 14, g32p_row02_traceSegment_002_1026_0013, g32p_row02_traceSegment_002_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1053 13 14, g32p_row02_traceSegment_002_1053_0013, g32p_row02_traceSegment_002_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1026 27 27, g32p_row02_traceSegment_002_1026_0027, g32p_row02_traceSegment_002_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 972 54 54, g32p_row02_traceSegment_002_0972_0054, g32p_row02_traceSegment_002_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 864 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 864 108 108, g32p_row02_traceSegment_002_0864_0108, g32p_row02_traceSegment_002_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1080 13 14, g32p_row02_traceSegment_002_1080_0013, g32p_row02_traceSegment_002_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1107 13 14, g32p_row02_traceSegment_002_1107_0013, g32p_row02_traceSegment_002_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1080 27 27, g32p_row02_traceSegment_002_1080_0027, g32p_row02_traceSegment_002_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1134 13 14, g32p_row02_traceSegment_002_1134_0013, g32p_row02_traceSegment_002_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1161 13 14, g32p_row02_traceSegment_002_1161_0013, g32p_row02_traceSegment_002_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1134 27 27, g32p_row02_traceSegment_002_1134_0027, g32p_row02_traceSegment_002_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1080 54 54, g32p_row02_traceSegment_002_1080_0054, g32p_row02_traceSegment_002_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1188 13 14, g32p_row02_traceSegment_002_1188_0013, g32p_row02_traceSegment_002_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1215 13 14, g32p_row02_traceSegment_002_1215_0013, g32p_row02_traceSegment_002_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1188 27 27, g32p_row02_traceSegment_002_1188_0027, g32p_row02_traceSegment_002_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1242 13 14, g32p_row02_traceSegment_002_1242_0013, g32p_row02_traceSegment_002_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1269 13 14, g32p_row02_traceSegment_002_1269_0013, g32p_row02_traceSegment_002_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1242 27 27, g32p_row02_traceSegment_002_1242_0027, g32p_row02_traceSegment_002_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1188 54 54, g32p_row02_traceSegment_002_1188_0054, g32p_row02_traceSegment_002_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1080 108 108, g32p_row02_traceSegment_002_1080_0108, g32p_row02_traceSegment_002_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_002 864 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 864 216 216, g32p_row02_traceSegment_002_0864_0216, g32p_row02_traceSegment_002_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1296 13 14, g32p_row02_traceSegment_002_1296_0013, g32p_row02_traceSegment_002_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1323 13 14, g32p_row02_traceSegment_002_1323_0013, g32p_row02_traceSegment_002_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1296 27 27, g32p_row02_traceSegment_002_1296_0027, g32p_row02_traceSegment_002_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1350 13 14, g32p_row02_traceSegment_002_1350_0013, g32p_row02_traceSegment_002_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1377 13 14, g32p_row02_traceSegment_002_1377_0013, g32p_row02_traceSegment_002_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1350 27 27, g32p_row02_traceSegment_002_1350_0027, g32p_row02_traceSegment_002_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1296 54 54, g32p_row02_traceSegment_002_1296_0054, g32p_row02_traceSegment_002_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1404 13 14, g32p_row02_traceSegment_002_1404_0013, g32p_row02_traceSegment_002_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1431 13 14, g32p_row02_traceSegment_002_1431_0013, g32p_row02_traceSegment_002_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1404 27 27, g32p_row02_traceSegment_002_1404_0027, g32p_row02_traceSegment_002_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1458 13 14, g32p_row02_traceSegment_002_1458_0013, g32p_row02_traceSegment_002_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1485 13 14, g32p_row02_traceSegment_002_1485_0013, g32p_row02_traceSegment_002_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1458 27 27, g32p_row02_traceSegment_002_1458_0027, g32p_row02_traceSegment_002_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1404 54 54, g32p_row02_traceSegment_002_1404_0054, g32p_row02_traceSegment_002_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1296 108 108, g32p_row02_traceSegment_002_1296_0108, g32p_row02_traceSegment_002_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1512 13 14, g32p_row02_traceSegment_002_1512_0013, g32p_row02_traceSegment_002_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1539 13 14, g32p_row02_traceSegment_002_1539_0013, g32p_row02_traceSegment_002_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1512 27 27, g32p_row02_traceSegment_002_1512_0027, g32p_row02_traceSegment_002_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1566 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1566 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1566 13 14, g32p_row02_traceSegment_002_1566_0013, g32p_row02_traceSegment_002_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1593 13 14, g32p_row02_traceSegment_002_1593_0013, g32p_row02_traceSegment_002_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1566 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1566 27 27, g32p_row02_traceSegment_002_1566_0027, g32p_row02_traceSegment_002_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 1512 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1512 54 54, g32p_row02_traceSegment_002_1512_0054, g32p_row02_traceSegment_002_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1620 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1620 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1620 13 14, g32p_row02_traceSegment_002_1620_0013, g32p_row02_traceSegment_002_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1647 13 14, g32p_row02_traceSegment_002_1647_0013, g32p_row02_traceSegment_002_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1620 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1620 27 27, g32p_row02_traceSegment_002_1620_0027, g32p_row02_traceSegment_002_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1674 13 14, g32p_row02_traceSegment_002_1674_0013, g32p_row02_traceSegment_002_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1701 13 14, g32p_row02_traceSegment_002_1701_0013, g32p_row02_traceSegment_002_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1674 27 27, g32p_row02_traceSegment_002_1674_0027, g32p_row02_traceSegment_002_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 1620 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1620 54 54, g32p_row02_traceSegment_002_1620_0054, g32p_row02_traceSegment_002_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 1512 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1512 108 108, g32p_row02_traceSegment_002_1512_0108, g32p_row02_traceSegment_002_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_002 1296 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1296 216 216, g32p_row02_traceSegment_002_1296_0216, g32p_row02_traceSegment_002_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_002 864 864 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 864 432 432, g32p_row02_traceSegment_002_0864_0432, g32p_row02_traceSegment_002_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_002 0 1728 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 0 864 864, g32p_row02_traceSegment_002_0000_0864, g32p_row02_traceSegment_002_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1728 13 14, g32p_row02_traceSegment_002_1728_0013, g32p_row02_traceSegment_002_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1755 13 14, g32p_row02_traceSegment_002_1755_0013, g32p_row02_traceSegment_002_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1728 27 27, g32p_row02_traceSegment_002_1728_0027, g32p_row02_traceSegment_002_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1782 13 14, g32p_row02_traceSegment_002_1782_0013, g32p_row02_traceSegment_002_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1809 13 14, g32p_row02_traceSegment_002_1809_0013, g32p_row02_traceSegment_002_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1782 27 27, g32p_row02_traceSegment_002_1782_0027, g32p_row02_traceSegment_002_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1728 54 54, g32p_row02_traceSegment_002_1728_0054, g32p_row02_traceSegment_002_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1836 13 14, g32p_row02_traceSegment_002_1836_0013, g32p_row02_traceSegment_002_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1863 13 14, g32p_row02_traceSegment_002_1863_0013, g32p_row02_traceSegment_002_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1836 27 27, g32p_row02_traceSegment_002_1836_0027, g32p_row02_traceSegment_002_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1890 13 14, g32p_row02_traceSegment_002_1890_0013, g32p_row02_traceSegment_002_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1917 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1917 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1917 13 14, g32p_row02_traceSegment_002_1917_0013, g32p_row02_traceSegment_002_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1890 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1890 27 27, g32p_row02_traceSegment_002_1890_0027, g32p_row02_traceSegment_002_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 1836 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1836 54 54, g32p_row02_traceSegment_002_1836_0054, g32p_row02_traceSegment_002_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 1728 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1728 108 108, g32p_row02_traceSegment_002_1728_0108, g32p_row02_traceSegment_002_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1944 13 14, g32p_row02_traceSegment_002_1944_0013, g32p_row02_traceSegment_002_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1971 13 14, g32p_row02_traceSegment_002_1971_0013, g32p_row02_traceSegment_002_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1944 27 27, g32p_row02_traceSegment_002_1944_0027, g32p_row02_traceSegment_002_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1998 13 14, g32p_row02_traceSegment_002_1998_0013, g32p_row02_traceSegment_002_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2025 13 14, g32p_row02_traceSegment_002_2025_0013, g32p_row02_traceSegment_002_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1998 27 27, g32p_row02_traceSegment_002_1998_0027, g32p_row02_traceSegment_002_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1944 54 54, g32p_row02_traceSegment_002_1944_0054, g32p_row02_traceSegment_002_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2052 13 14, g32p_row02_traceSegment_002_2052_0013, g32p_row02_traceSegment_002_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2079 13 14, g32p_row02_traceSegment_002_2079_0013, g32p_row02_traceSegment_002_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2052 27 27, g32p_row02_traceSegment_002_2052_0027, g32p_row02_traceSegment_002_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2106 13 14, g32p_row02_traceSegment_002_2106_0013, g32p_row02_traceSegment_002_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2133 13 14, g32p_row02_traceSegment_002_2133_0013, g32p_row02_traceSegment_002_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2106 27 27, g32p_row02_traceSegment_002_2106_0027, g32p_row02_traceSegment_002_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2052 54 54, g32p_row02_traceSegment_002_2052_0054, g32p_row02_traceSegment_002_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1944 108 108, g32p_row02_traceSegment_002_1944_0108, g32p_row02_traceSegment_002_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_002 1728 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1728 216 216, g32p_row02_traceSegment_002_1728_0216, g32p_row02_traceSegment_002_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2160 13 14, g32p_row02_traceSegment_002_2160_0013, g32p_row02_traceSegment_002_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2187 13 14, g32p_row02_traceSegment_002_2187_0013, g32p_row02_traceSegment_002_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2160 27 27, g32p_row02_traceSegment_002_2160_0027, g32p_row02_traceSegment_002_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2214 13 14, g32p_row02_traceSegment_002_2214_0013, g32p_row02_traceSegment_002_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2241 13 14, g32p_row02_traceSegment_002_2241_0013, g32p_row02_traceSegment_002_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2214 27 27, g32p_row02_traceSegment_002_2214_0027, g32p_row02_traceSegment_002_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2160 54 54, g32p_row02_traceSegment_002_2160_0054, g32p_row02_traceSegment_002_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2268 13 14, g32p_row02_traceSegment_002_2268_0013, g32p_row02_traceSegment_002_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2295 13 14, g32p_row02_traceSegment_002_2295_0013, g32p_row02_traceSegment_002_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2268 27 27, g32p_row02_traceSegment_002_2268_0027, g32p_row02_traceSegment_002_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2322 13 14, g32p_row02_traceSegment_002_2322_0013, g32p_row02_traceSegment_002_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2349 13 14, g32p_row02_traceSegment_002_2349_0013, g32p_row02_traceSegment_002_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2322 27 27, g32p_row02_traceSegment_002_2322_0027, g32p_row02_traceSegment_002_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2268 54 54, g32p_row02_traceSegment_002_2268_0054, g32p_row02_traceSegment_002_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2160 108 108, g32p_row02_traceSegment_002_2160_0108, g32p_row02_traceSegment_002_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2376 13 14, g32p_row02_traceSegment_002_2376_0013, g32p_row02_traceSegment_002_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2403 13 14, g32p_row02_traceSegment_002_2403_0013, g32p_row02_traceSegment_002_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2376 27 27, g32p_row02_traceSegment_002_2376_0027, g32p_row02_traceSegment_002_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2430 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2430 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2430 13 14, g32p_row02_traceSegment_002_2430_0013, g32p_row02_traceSegment_002_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2457 13 14, g32p_row02_traceSegment_002_2457_0013, g32p_row02_traceSegment_002_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2430 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2430 27 27, g32p_row02_traceSegment_002_2430_0027, g32p_row02_traceSegment_002_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 2376 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2376 54 54, g32p_row02_traceSegment_002_2376_0054, g32p_row02_traceSegment_002_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2484 13 14, g32p_row02_traceSegment_002_2484_0013, g32p_row02_traceSegment_002_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2511 13 14, g32p_row02_traceSegment_002_2511_0013, g32p_row02_traceSegment_002_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2484 27 27, g32p_row02_traceSegment_002_2484_0027, g32p_row02_traceSegment_002_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2538 13 14, g32p_row02_traceSegment_002_2538_0013, g32p_row02_traceSegment_002_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2565 13 14, g32p_row02_traceSegment_002_2565_0013, g32p_row02_traceSegment_002_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2538 27 27, g32p_row02_traceSegment_002_2538_0027, g32p_row02_traceSegment_002_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2484 54 54, g32p_row02_traceSegment_002_2484_0054, g32p_row02_traceSegment_002_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 2376 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2376 108 108, g32p_row02_traceSegment_002_2376_0108, g32p_row02_traceSegment_002_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_002 2160 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2160 216 216, g32p_row02_traceSegment_002_2160_0216, g32p_row02_traceSegment_002_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_002 1728 864 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1728 432 432, g32p_row02_traceSegment_002_1728_0432, g32p_row02_traceSegment_002_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2592 13 14, g32p_row02_traceSegment_002_2592_0013, g32p_row02_traceSegment_002_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2619 13 14, g32p_row02_traceSegment_002_2619_0013, g32p_row02_traceSegment_002_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2592 27 27, g32p_row02_traceSegment_002_2592_0027, g32p_row02_traceSegment_002_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2646 13 14, g32p_row02_traceSegment_002_2646_0013, g32p_row02_traceSegment_002_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2673 13 14, g32p_row02_traceSegment_002_2673_0013, g32p_row02_traceSegment_002_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2646 27 27, g32p_row02_traceSegment_002_2646_0027, g32p_row02_traceSegment_002_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2592 54 54, g32p_row02_traceSegment_002_2592_0054, g32p_row02_traceSegment_002_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2700 13 14, g32p_row02_traceSegment_002_2700_0013, g32p_row02_traceSegment_002_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2727 13 14, g32p_row02_traceSegment_002_2727_0013, g32p_row02_traceSegment_002_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2700 27 27, g32p_row02_traceSegment_002_2700_0027, g32p_row02_traceSegment_002_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2754 13 14, g32p_row02_traceSegment_002_2754_0013, g32p_row02_traceSegment_002_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2781 13 14, g32p_row02_traceSegment_002_2781_0013, g32p_row02_traceSegment_002_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2754 27 27, g32p_row02_traceSegment_002_2754_0027, g32p_row02_traceSegment_002_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2700 54 54, g32p_row02_traceSegment_002_2700_0054, g32p_row02_traceSegment_002_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2592 108 108, g32p_row02_traceSegment_002_2592_0108, g32p_row02_traceSegment_002_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2808 13 14, g32p_row02_traceSegment_002_2808_0013, g32p_row02_traceSegment_002_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2835 13 14, g32p_row02_traceSegment_002_2835_0013, g32p_row02_traceSegment_002_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2808 27 27, g32p_row02_traceSegment_002_2808_0027, g32p_row02_traceSegment_002_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2862 13 14, g32p_row02_traceSegment_002_2862_0013, g32p_row02_traceSegment_002_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2889 13 14, g32p_row02_traceSegment_002_2889_0013, g32p_row02_traceSegment_002_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2862 27 27, g32p_row02_traceSegment_002_2862_0027, g32p_row02_traceSegment_002_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2808 54 54, g32p_row02_traceSegment_002_2808_0054, g32p_row02_traceSegment_002_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2916 13 14, g32p_row02_traceSegment_002_2916_0013, g32p_row02_traceSegment_002_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2943 13 14, g32p_row02_traceSegment_002_2943_0013, g32p_row02_traceSegment_002_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2916 27 27, g32p_row02_traceSegment_002_2916_0027, g32p_row02_traceSegment_002_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2970 13 14, g32p_row02_traceSegment_002_2970_0013, g32p_row02_traceSegment_002_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2997 13 14, g32p_row02_traceSegment_002_2997_0013, g32p_row02_traceSegment_002_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2970 27 27, g32p_row02_traceSegment_002_2970_0027, g32p_row02_traceSegment_002_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2916 54 54, g32p_row02_traceSegment_002_2916_0054, g32p_row02_traceSegment_002_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2808 108 108, g32p_row02_traceSegment_002_2808_0108, g32p_row02_traceSegment_002_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_002 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2592 216 216, g32p_row02_traceSegment_002_2592_0216, g32p_row02_traceSegment_002_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3024 13 14, g32p_row02_traceSegment_002_3024_0013, g32p_row02_traceSegment_002_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3051 13 14, g32p_row02_traceSegment_002_3051_0013, g32p_row02_traceSegment_002_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3024 27 27, g32p_row02_traceSegment_002_3024_0027, g32p_row02_traceSegment_002_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3078 13 14, g32p_row02_traceSegment_002_3078_0013, g32p_row02_traceSegment_002_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3105 13 14, g32p_row02_traceSegment_002_3105_0013, g32p_row02_traceSegment_002_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3078 27 27, g32p_row02_traceSegment_002_3078_0027, g32p_row02_traceSegment_002_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3024 54 54, g32p_row02_traceSegment_002_3024_0054, g32p_row02_traceSegment_002_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3132 13 14, g32p_row02_traceSegment_002_3132_0013, g32p_row02_traceSegment_002_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3159 13 14, g32p_row02_traceSegment_002_3159_0013, g32p_row02_traceSegment_002_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3132 27 27, g32p_row02_traceSegment_002_3132_0027, g32p_row02_traceSegment_002_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3186 13 14, g32p_row02_traceSegment_002_3186_0013, g32p_row02_traceSegment_002_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3213 13 14, g32p_row02_traceSegment_002_3213_0013, g32p_row02_traceSegment_002_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3186 27 27, g32p_row02_traceSegment_002_3186_0027, g32p_row02_traceSegment_002_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3132 54 54, g32p_row02_traceSegment_002_3132_0054, g32p_row02_traceSegment_002_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3024 108 108, g32p_row02_traceSegment_002_3024_0108, g32p_row02_traceSegment_002_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3240 13 14, g32p_row02_traceSegment_002_3240_0013, g32p_row02_traceSegment_002_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3267 13 14, g32p_row02_traceSegment_002_3267_0013, g32p_row02_traceSegment_002_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3240 27 27, g32p_row02_traceSegment_002_3240_0027, g32p_row02_traceSegment_002_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3294 13 14, g32p_row02_traceSegment_002_3294_0013, g32p_row02_traceSegment_002_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3321 13 14, g32p_row02_traceSegment_002_3321_0013, g32p_row02_traceSegment_002_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3294 27 27, g32p_row02_traceSegment_002_3294_0027, g32p_row02_traceSegment_002_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3240 54 54, g32p_row02_traceSegment_002_3240_0054, g32p_row02_traceSegment_002_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3348 13 14, g32p_row02_traceSegment_002_3348_0013, g32p_row02_traceSegment_002_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3375 13 14, g32p_row02_traceSegment_002_3375_0013, g32p_row02_traceSegment_002_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3348 27 27, g32p_row02_traceSegment_002_3348_0027, g32p_row02_traceSegment_002_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3402 13 14, g32p_row02_traceSegment_002_3402_0013, g32p_row02_traceSegment_002_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_002 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_002 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_002_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_002 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3429 13 14, g32p_row02_traceSegment_002_3429_0013, g32p_row02_traceSegment_002_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_002 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3402 27 27, g32p_row02_traceSegment_002_3402_0027, g32p_row02_traceSegment_002_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_002 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3348 54 54, g32p_row02_traceSegment_002_3348_0054, g32p_row02_traceSegment_002_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_002 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3240 108 108, g32p_row02_traceSegment_002_3240_0108, g32p_row02_traceSegment_002_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_002_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_002 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 3024 216 216, g32p_row02_traceSegment_002_3024_0216, g32p_row02_traceSegment_002_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_002_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_002 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 2592 432 432, g32p_row02_traceSegment_002_2592_0432, g32p_row02_traceSegment_002_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_002_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_002 1728 1728 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 1728 864 864, g32p_row02_traceSegment_002_1728_0864, g32p_row02_traceSegment_002_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_002_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_002 0 3456 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_002 0 1728 1728, g32p_row02_traceSegment_002_0000_1728, g32p_row02_traceSegment_002_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 2 = [8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_002_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_003 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 3 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_003_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 0 13 14, g32p_row02_traceSegment_003_0000_0013, g32p_row02_traceSegment_003_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 27 13 14, g32p_row02_traceSegment_003_0027_0013, g32p_row02_traceSegment_003_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 0 27 27, g32p_row02_traceSegment_003_0000_0027, g32p_row02_traceSegment_003_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 54 13 14, g32p_row02_traceSegment_003_0054_0013, g32p_row02_traceSegment_003_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 81 13 14, g32p_row02_traceSegment_003_0081_0013, g32p_row02_traceSegment_003_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 54 27 27, g32p_row02_traceSegment_003_0054_0027, g32p_row02_traceSegment_003_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 0 54 54, g32p_row02_traceSegment_003_0000_0054, g32p_row02_traceSegment_003_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 108 13 14, g32p_row02_traceSegment_003_0108_0013, g32p_row02_traceSegment_003_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 135 13 14, g32p_row02_traceSegment_003_0135_0013, g32p_row02_traceSegment_003_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 108 27 27, g32p_row02_traceSegment_003_0108_0027, g32p_row02_traceSegment_003_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 162 13 14, g32p_row02_traceSegment_003_0162_0013, g32p_row02_traceSegment_003_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 189 13 14, g32p_row02_traceSegment_003_0189_0013, g32p_row02_traceSegment_003_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 162 27 27, g32p_row02_traceSegment_003_0162_0027, g32p_row02_traceSegment_003_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 108 54 54, g32p_row02_traceSegment_003_0108_0054, g32p_row02_traceSegment_003_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 0 108 108, g32p_row02_traceSegment_003_0000_0108, g32p_row02_traceSegment_003_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 216 13 14, g32p_row02_traceSegment_003_0216_0013, g32p_row02_traceSegment_003_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 243 13 14, g32p_row02_traceSegment_003_0243_0013, g32p_row02_traceSegment_003_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 216 27 27, g32p_row02_traceSegment_003_0216_0027, g32p_row02_traceSegment_003_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 270 13 14, g32p_row02_traceSegment_003_0270_0013, g32p_row02_traceSegment_003_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 297 13 14, g32p_row02_traceSegment_003_0297_0013, g32p_row02_traceSegment_003_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 270 27 27, g32p_row02_traceSegment_003_0270_0027, g32p_row02_traceSegment_003_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 216 54 54, g32p_row02_traceSegment_003_0216_0054, g32p_row02_traceSegment_003_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 324 13 14, g32p_row02_traceSegment_003_0324_0013, g32p_row02_traceSegment_003_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 351 13 14, g32p_row02_traceSegment_003_0351_0013, g32p_row02_traceSegment_003_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 324 27 27, g32p_row02_traceSegment_003_0324_0027, g32p_row02_traceSegment_003_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 378 13 14, g32p_row02_traceSegment_003_0378_0013, g32p_row02_traceSegment_003_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 405 13 14, g32p_row02_traceSegment_003_0405_0013, g32p_row02_traceSegment_003_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 378 27 27, g32p_row02_traceSegment_003_0378_0027, g32p_row02_traceSegment_003_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 324 54 54, g32p_row02_traceSegment_003_0324_0054, g32p_row02_traceSegment_003_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 216 108 108, g32p_row02_traceSegment_003_0216_0108, g32p_row02_traceSegment_003_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_003 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 0 216 216, g32p_row02_traceSegment_003_0000_0216, g32p_row02_traceSegment_003_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 432 13 14, g32p_row02_traceSegment_003_0432_0013, g32p_row02_traceSegment_003_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 459 13 14, g32p_row02_traceSegment_003_0459_0013, g32p_row02_traceSegment_003_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 432 27 27, g32p_row02_traceSegment_003_0432_0027, g32p_row02_traceSegment_003_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 486 13 14, g32p_row02_traceSegment_003_0486_0013, g32p_row02_traceSegment_003_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 513 13 14, g32p_row02_traceSegment_003_0513_0013, g32p_row02_traceSegment_003_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 486 27 27, g32p_row02_traceSegment_003_0486_0027, g32p_row02_traceSegment_003_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 432 54 54, g32p_row02_traceSegment_003_0432_0054, g32p_row02_traceSegment_003_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 540 13 14, g32p_row02_traceSegment_003_0540_0013, g32p_row02_traceSegment_003_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 567 13 14, g32p_row02_traceSegment_003_0567_0013, g32p_row02_traceSegment_003_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 540 27 27, g32p_row02_traceSegment_003_0540_0027, g32p_row02_traceSegment_003_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 594 13 14, g32p_row02_traceSegment_003_0594_0013, g32p_row02_traceSegment_003_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 621 13 14, g32p_row02_traceSegment_003_0621_0013, g32p_row02_traceSegment_003_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 594 27 27, g32p_row02_traceSegment_003_0594_0027, g32p_row02_traceSegment_003_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 540 54 54, g32p_row02_traceSegment_003_0540_0054, g32p_row02_traceSegment_003_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 432 108 108, g32p_row02_traceSegment_003_0432_0108, g32p_row02_traceSegment_003_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 648 13 14, g32p_row02_traceSegment_003_0648_0013, g32p_row02_traceSegment_003_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 675 13 14, g32p_row02_traceSegment_003_0675_0013, g32p_row02_traceSegment_003_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 648 27 27, g32p_row02_traceSegment_003_0648_0027, g32p_row02_traceSegment_003_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 702 13 14, g32p_row02_traceSegment_003_0702_0013, g32p_row02_traceSegment_003_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 729 13 14, g32p_row02_traceSegment_003_0729_0013, g32p_row02_traceSegment_003_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 702 27 27, g32p_row02_traceSegment_003_0702_0027, g32p_row02_traceSegment_003_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 648 54 54, g32p_row02_traceSegment_003_0648_0054, g32p_row02_traceSegment_003_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 756 13 14, g32p_row02_traceSegment_003_0756_0013, g32p_row02_traceSegment_003_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 783 13 14, g32p_row02_traceSegment_003_0783_0013, g32p_row02_traceSegment_003_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 756 27 27, g32p_row02_traceSegment_003_0756_0027, g32p_row02_traceSegment_003_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 810 13 14, g32p_row02_traceSegment_003_0810_0013, g32p_row02_traceSegment_003_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 837 13 14, g32p_row02_traceSegment_003_0837_0013, g32p_row02_traceSegment_003_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 810 27 27, g32p_row02_traceSegment_003_0810_0027, g32p_row02_traceSegment_003_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 756 54 54, g32p_row02_traceSegment_003_0756_0054, g32p_row02_traceSegment_003_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 648 108 108, g32p_row02_traceSegment_003_0648_0108, g32p_row02_traceSegment_003_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_003 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 432 216 216, g32p_row02_traceSegment_003_0432_0216, g32p_row02_traceSegment_003_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_003 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 0 432 432, g32p_row02_traceSegment_003_0000_0432, g32p_row02_traceSegment_003_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 864 13 14, g32p_row02_traceSegment_003_0864_0013, g32p_row02_traceSegment_003_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 891 13 14, g32p_row02_traceSegment_003_0891_0013, g32p_row02_traceSegment_003_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 864 27 27, g32p_row02_traceSegment_003_0864_0027, g32p_row02_traceSegment_003_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 918 13 14, g32p_row02_traceSegment_003_0918_0013, g32p_row02_traceSegment_003_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 945 13 14, g32p_row02_traceSegment_003_0945_0013, g32p_row02_traceSegment_003_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 918 27 27, g32p_row02_traceSegment_003_0918_0027, g32p_row02_traceSegment_003_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 864 54 54, g32p_row02_traceSegment_003_0864_0054, g32p_row02_traceSegment_003_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 972 13 14, g32p_row02_traceSegment_003_0972_0013, g32p_row02_traceSegment_003_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 999 13 14, g32p_row02_traceSegment_003_0999_0013, g32p_row02_traceSegment_003_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 972 27 27, g32p_row02_traceSegment_003_0972_0027, g32p_row02_traceSegment_003_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1026 13 14, g32p_row02_traceSegment_003_1026_0013, g32p_row02_traceSegment_003_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1053 13 14, g32p_row02_traceSegment_003_1053_0013, g32p_row02_traceSegment_003_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1026 27 27, g32p_row02_traceSegment_003_1026_0027, g32p_row02_traceSegment_003_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 972 54 54, g32p_row02_traceSegment_003_0972_0054, g32p_row02_traceSegment_003_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 864 108 108, g32p_row02_traceSegment_003_0864_0108, g32p_row02_traceSegment_003_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1080 13 14, g32p_row02_traceSegment_003_1080_0013, g32p_row02_traceSegment_003_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1107 13 14, g32p_row02_traceSegment_003_1107_0013, g32p_row02_traceSegment_003_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1080 27 27, g32p_row02_traceSegment_003_1080_0027, g32p_row02_traceSegment_003_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1134 13 14, g32p_row02_traceSegment_003_1134_0013, g32p_row02_traceSegment_003_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1161 13 14, g32p_row02_traceSegment_003_1161_0013, g32p_row02_traceSegment_003_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1134 27 27, g32p_row02_traceSegment_003_1134_0027, g32p_row02_traceSegment_003_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1080 54 54, g32p_row02_traceSegment_003_1080_0054, g32p_row02_traceSegment_003_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1188 13 14, g32p_row02_traceSegment_003_1188_0013, g32p_row02_traceSegment_003_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1215 13 14, g32p_row02_traceSegment_003_1215_0013, g32p_row02_traceSegment_003_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1188 27 27, g32p_row02_traceSegment_003_1188_0027, g32p_row02_traceSegment_003_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1242 13 14, g32p_row02_traceSegment_003_1242_0013, g32p_row02_traceSegment_003_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1269 13 14, g32p_row02_traceSegment_003_1269_0013, g32p_row02_traceSegment_003_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1242 27 27, g32p_row02_traceSegment_003_1242_0027, g32p_row02_traceSegment_003_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1188 54 54, g32p_row02_traceSegment_003_1188_0054, g32p_row02_traceSegment_003_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1080 108 108, g32p_row02_traceSegment_003_1080_0108, g32p_row02_traceSegment_003_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_003 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 864 216 216, g32p_row02_traceSegment_003_0864_0216, g32p_row02_traceSegment_003_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1296 13 14, g32p_row02_traceSegment_003_1296_0013, g32p_row02_traceSegment_003_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1323 13 14, g32p_row02_traceSegment_003_1323_0013, g32p_row02_traceSegment_003_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1296 27 27, g32p_row02_traceSegment_003_1296_0027, g32p_row02_traceSegment_003_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1350 13 14, g32p_row02_traceSegment_003_1350_0013, g32p_row02_traceSegment_003_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1377 13 14, g32p_row02_traceSegment_003_1377_0013, g32p_row02_traceSegment_003_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1350 27 27, g32p_row02_traceSegment_003_1350_0027, g32p_row02_traceSegment_003_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1296 54 54, g32p_row02_traceSegment_003_1296_0054, g32p_row02_traceSegment_003_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1404 13 14, g32p_row02_traceSegment_003_1404_0013, g32p_row02_traceSegment_003_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1431 13 14, g32p_row02_traceSegment_003_1431_0013, g32p_row02_traceSegment_003_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1404 27 27, g32p_row02_traceSegment_003_1404_0027, g32p_row02_traceSegment_003_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1458 13 14, g32p_row02_traceSegment_003_1458_0013, g32p_row02_traceSegment_003_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1485 13 14, g32p_row02_traceSegment_003_1485_0013, g32p_row02_traceSegment_003_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1458 27 27, g32p_row02_traceSegment_003_1458_0027, g32p_row02_traceSegment_003_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1404 54 54, g32p_row02_traceSegment_003_1404_0054, g32p_row02_traceSegment_003_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1296 108 108, g32p_row02_traceSegment_003_1296_0108, g32p_row02_traceSegment_003_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1512 13 14, g32p_row02_traceSegment_003_1512_0013, g32p_row02_traceSegment_003_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1539 13 14, g32p_row02_traceSegment_003_1539_0013, g32p_row02_traceSegment_003_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1512 27 27, g32p_row02_traceSegment_003_1512_0027, g32p_row02_traceSegment_003_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1566 13 14, g32p_row02_traceSegment_003_1566_0013, g32p_row02_traceSegment_003_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1593 13 14, g32p_row02_traceSegment_003_1593_0013, g32p_row02_traceSegment_003_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1566 27 27, g32p_row02_traceSegment_003_1566_0027, g32p_row02_traceSegment_003_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1512 54 54, g32p_row02_traceSegment_003_1512_0054, g32p_row02_traceSegment_003_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1620 13 14, g32p_row02_traceSegment_003_1620_0013, g32p_row02_traceSegment_003_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1647 13 14, g32p_row02_traceSegment_003_1647_0013, g32p_row02_traceSegment_003_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1620 27 27, g32p_row02_traceSegment_003_1620_0027, g32p_row02_traceSegment_003_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1674 13 14, g32p_row02_traceSegment_003_1674_0013, g32p_row02_traceSegment_003_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1701 13 14, g32p_row02_traceSegment_003_1701_0013, g32p_row02_traceSegment_003_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1674 27 27, g32p_row02_traceSegment_003_1674_0027, g32p_row02_traceSegment_003_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1620 54 54, g32p_row02_traceSegment_003_1620_0054, g32p_row02_traceSegment_003_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1512 108 108, g32p_row02_traceSegment_003_1512_0108, g32p_row02_traceSegment_003_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_003 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1296 216 216, g32p_row02_traceSegment_003_1296_0216, g32p_row02_traceSegment_003_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_003 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 864 432 432, g32p_row02_traceSegment_003_0864_0432, g32p_row02_traceSegment_003_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_003 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 0 864 864, g32p_row02_traceSegment_003_0000_0864, g32p_row02_traceSegment_003_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1728 13 14, g32p_row02_traceSegment_003_1728_0013, g32p_row02_traceSegment_003_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1755 13 14, g32p_row02_traceSegment_003_1755_0013, g32p_row02_traceSegment_003_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1728 27 27, g32p_row02_traceSegment_003_1728_0027, g32p_row02_traceSegment_003_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1782 13 14, g32p_row02_traceSegment_003_1782_0013, g32p_row02_traceSegment_003_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1809 13 14, g32p_row02_traceSegment_003_1809_0013, g32p_row02_traceSegment_003_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1782 27 27, g32p_row02_traceSegment_003_1782_0027, g32p_row02_traceSegment_003_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1728 54 54, g32p_row02_traceSegment_003_1728_0054, g32p_row02_traceSegment_003_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1836 13 14, g32p_row02_traceSegment_003_1836_0013, g32p_row02_traceSegment_003_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1863 13 14, g32p_row02_traceSegment_003_1863_0013, g32p_row02_traceSegment_003_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1836 27 27, g32p_row02_traceSegment_003_1836_0027, g32p_row02_traceSegment_003_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1890 13 14, g32p_row02_traceSegment_003_1890_0013, g32p_row02_traceSegment_003_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1917 13 14, g32p_row02_traceSegment_003_1917_0013, g32p_row02_traceSegment_003_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1890 27 27, g32p_row02_traceSegment_003_1890_0027, g32p_row02_traceSegment_003_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1836 54 54, g32p_row02_traceSegment_003_1836_0054, g32p_row02_traceSegment_003_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1728 108 108, g32p_row02_traceSegment_003_1728_0108, g32p_row02_traceSegment_003_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1944 13 14, g32p_row02_traceSegment_003_1944_0013, g32p_row02_traceSegment_003_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1971 13 14, g32p_row02_traceSegment_003_1971_0013, g32p_row02_traceSegment_003_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1944 27 27, g32p_row02_traceSegment_003_1944_0027, g32p_row02_traceSegment_003_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1998 13 14, g32p_row02_traceSegment_003_1998_0013, g32p_row02_traceSegment_003_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2025 13 14, g32p_row02_traceSegment_003_2025_0013, g32p_row02_traceSegment_003_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1998 27 27, g32p_row02_traceSegment_003_1998_0027, g32p_row02_traceSegment_003_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1944 54 54, g32p_row02_traceSegment_003_1944_0054, g32p_row02_traceSegment_003_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2052 13 14, g32p_row02_traceSegment_003_2052_0013, g32p_row02_traceSegment_003_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2079 13 14, g32p_row02_traceSegment_003_2079_0013, g32p_row02_traceSegment_003_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2052 27 27, g32p_row02_traceSegment_003_2052_0027, g32p_row02_traceSegment_003_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2106 13 14, g32p_row02_traceSegment_003_2106_0013, g32p_row02_traceSegment_003_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2133 13 14, g32p_row02_traceSegment_003_2133_0013, g32p_row02_traceSegment_003_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2106 27 27, g32p_row02_traceSegment_003_2106_0027, g32p_row02_traceSegment_003_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2052 54 54, g32p_row02_traceSegment_003_2052_0054, g32p_row02_traceSegment_003_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1944 108 108, g32p_row02_traceSegment_003_1944_0108, g32p_row02_traceSegment_003_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_003 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1728 216 216, g32p_row02_traceSegment_003_1728_0216, g32p_row02_traceSegment_003_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2160 13 14, g32p_row02_traceSegment_003_2160_0013, g32p_row02_traceSegment_003_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2187 13 14, g32p_row02_traceSegment_003_2187_0013, g32p_row02_traceSegment_003_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2160 27 27, g32p_row02_traceSegment_003_2160_0027, g32p_row02_traceSegment_003_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2214 13 14, g32p_row02_traceSegment_003_2214_0013, g32p_row02_traceSegment_003_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2241 13 14, g32p_row02_traceSegment_003_2241_0013, g32p_row02_traceSegment_003_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2214 27 27, g32p_row02_traceSegment_003_2214_0027, g32p_row02_traceSegment_003_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2160 54 54, g32p_row02_traceSegment_003_2160_0054, g32p_row02_traceSegment_003_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2268 13 14, g32p_row02_traceSegment_003_2268_0013, g32p_row02_traceSegment_003_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2295 13 14, g32p_row02_traceSegment_003_2295_0013, g32p_row02_traceSegment_003_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2268 27 27, g32p_row02_traceSegment_003_2268_0027, g32p_row02_traceSegment_003_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2322 13 14, g32p_row02_traceSegment_003_2322_0013, g32p_row02_traceSegment_003_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2349 13 14, g32p_row02_traceSegment_003_2349_0013, g32p_row02_traceSegment_003_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2322 27 27, g32p_row02_traceSegment_003_2322_0027, g32p_row02_traceSegment_003_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2268 54 54, g32p_row02_traceSegment_003_2268_0054, g32p_row02_traceSegment_003_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2160 108 108, g32p_row02_traceSegment_003_2160_0108, g32p_row02_traceSegment_003_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2376 13 14, g32p_row02_traceSegment_003_2376_0013, g32p_row02_traceSegment_003_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2403 13 14, g32p_row02_traceSegment_003_2403_0013, g32p_row02_traceSegment_003_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2376 27 27, g32p_row02_traceSegment_003_2376_0027, g32p_row02_traceSegment_003_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2430 13 14, g32p_row02_traceSegment_003_2430_0013, g32p_row02_traceSegment_003_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2457 13 14, g32p_row02_traceSegment_003_2457_0013, g32p_row02_traceSegment_003_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2430 27 27, g32p_row02_traceSegment_003_2430_0027, g32p_row02_traceSegment_003_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2376 54 54, g32p_row02_traceSegment_003_2376_0054, g32p_row02_traceSegment_003_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2484 13 14, g32p_row02_traceSegment_003_2484_0013, g32p_row02_traceSegment_003_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2511 13 14, g32p_row02_traceSegment_003_2511_0013, g32p_row02_traceSegment_003_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2484 27 27, g32p_row02_traceSegment_003_2484_0027, g32p_row02_traceSegment_003_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2538 13 14, g32p_row02_traceSegment_003_2538_0013, g32p_row02_traceSegment_003_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2565 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2578 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2565 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2565 13 14, g32p_row02_traceSegment_003_2565_0013, g32p_row02_traceSegment_003_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2538 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2538 27 27, g32p_row02_traceSegment_003_2538_0027, g32p_row02_traceSegment_003_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 2484 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2484 54 54, g32p_row02_traceSegment_003_2484_0054, g32p_row02_traceSegment_003_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 2376 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2376 108 108, g32p_row02_traceSegment_003_2376_0108, g32p_row02_traceSegment_003_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_003 2160 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2160 216 216, g32p_row02_traceSegment_003_2160_0216, g32p_row02_traceSegment_003_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_003 1728 864 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1728 432 432, g32p_row02_traceSegment_003_1728_0432, g32p_row02_traceSegment_003_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2592 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2592 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2592 13 14, g32p_row02_traceSegment_003_2592_0013, g32p_row02_traceSegment_003_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2619 13 14, g32p_row02_traceSegment_003_2619_0013, g32p_row02_traceSegment_003_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2592 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2592 27 27, g32p_row02_traceSegment_003_2592_0027, g32p_row02_traceSegment_003_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2646 13 14, g32p_row02_traceSegment_003_2646_0013, g32p_row02_traceSegment_003_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2673 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2686 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2673 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2673 13 14, g32p_row02_traceSegment_003_2673_0013, g32p_row02_traceSegment_003_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2646 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2646 27 27, g32p_row02_traceSegment_003_2646_0027, g32p_row02_traceSegment_003_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 2592 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2592 54 54, g32p_row02_traceSegment_003_2592_0054, g32p_row02_traceSegment_003_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2700 13 14, g32p_row02_traceSegment_003_2700_0013, g32p_row02_traceSegment_003_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2727 13 14, g32p_row02_traceSegment_003_2727_0013, g32p_row02_traceSegment_003_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2700 27 27, g32p_row02_traceSegment_003_2700_0027, g32p_row02_traceSegment_003_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2754 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2754 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2754 13 14, g32p_row02_traceSegment_003_2754_0013, g32p_row02_traceSegment_003_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2781 13 14, g32p_row02_traceSegment_003_2781_0013, g32p_row02_traceSegment_003_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2754 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2754 27 27, g32p_row02_traceSegment_003_2754_0027, g32p_row02_traceSegment_003_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 2700 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2700 54 54, g32p_row02_traceSegment_003_2700_0054, g32p_row02_traceSegment_003_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 2592 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2592 108 108, g32p_row02_traceSegment_003_2592_0108, g32p_row02_traceSegment_003_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2808 13 14, g32p_row02_traceSegment_003_2808_0013, g32p_row02_traceSegment_003_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2848 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2835 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2835 13 14, g32p_row02_traceSegment_003_2835_0013, g32p_row02_traceSegment_003_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2808 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2808 27 27, g32p_row02_traceSegment_003_2808_0027, g32p_row02_traceSegment_003_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2862 13 14, g32p_row02_traceSegment_003_2862_0013, g32p_row02_traceSegment_003_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2889 13 14, g32p_row02_traceSegment_003_2889_0013, g32p_row02_traceSegment_003_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2862 27 27, g32p_row02_traceSegment_003_2862_0027, g32p_row02_traceSegment_003_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 2808 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2808 54 54, g32p_row02_traceSegment_003_2808_0054, g32p_row02_traceSegment_003_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2916 13 14, g32p_row02_traceSegment_003_2916_0013, g32p_row02_traceSegment_003_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2943 13 14, g32p_row02_traceSegment_003_2943_0013, g32p_row02_traceSegment_003_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2916 27 27, g32p_row02_traceSegment_003_2916_0027, g32p_row02_traceSegment_003_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2970 13 14, g32p_row02_traceSegment_003_2970_0013, g32p_row02_traceSegment_003_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 2997 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 2997 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2997 13 14, g32p_row02_traceSegment_003_2997_0013, g32p_row02_traceSegment_003_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 2970 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2970 27 27, g32p_row02_traceSegment_003_2970_0027, g32p_row02_traceSegment_003_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 2916 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2916 54 54, g32p_row02_traceSegment_003_2916_0054, g32p_row02_traceSegment_003_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 2808 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2808 108 108, g32p_row02_traceSegment_003_2808_0108, g32p_row02_traceSegment_003_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_003 2592 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2592 216 216, g32p_row02_traceSegment_003_2592_0216, g32p_row02_traceSegment_003_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3024 13 14, g32p_row02_traceSegment_003_3024_0013, g32p_row02_traceSegment_003_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3051 13 14, g32p_row02_traceSegment_003_3051_0013, g32p_row02_traceSegment_003_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3024 27 27, g32p_row02_traceSegment_003_3024_0027, g32p_row02_traceSegment_003_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3078 13 14, g32p_row02_traceSegment_003_3078_0013, g32p_row02_traceSegment_003_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3105 13 14, g32p_row02_traceSegment_003_3105_0013, g32p_row02_traceSegment_003_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3078 27 27, g32p_row02_traceSegment_003_3078_0027, g32p_row02_traceSegment_003_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3024 54 54, g32p_row02_traceSegment_003_3024_0054, g32p_row02_traceSegment_003_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3132 13 14, g32p_row02_traceSegment_003_3132_0013, g32p_row02_traceSegment_003_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3159 13 14, g32p_row02_traceSegment_003_3159_0013, g32p_row02_traceSegment_003_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3132 27 27, g32p_row02_traceSegment_003_3132_0027, g32p_row02_traceSegment_003_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3186 13 14, g32p_row02_traceSegment_003_3186_0013, g32p_row02_traceSegment_003_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3213 13 14, g32p_row02_traceSegment_003_3213_0013, g32p_row02_traceSegment_003_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3186 27 27, g32p_row02_traceSegment_003_3186_0027, g32p_row02_traceSegment_003_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3132 54 54, g32p_row02_traceSegment_003_3132_0054, g32p_row02_traceSegment_003_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3024 108 108, g32p_row02_traceSegment_003_3024_0108, g32p_row02_traceSegment_003_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3240 13 14, g32p_row02_traceSegment_003_3240_0013, g32p_row02_traceSegment_003_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3267 13 14, g32p_row02_traceSegment_003_3267_0013, g32p_row02_traceSegment_003_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3240 27 27, g32p_row02_traceSegment_003_3240_0027, g32p_row02_traceSegment_003_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3294 13 14, g32p_row02_traceSegment_003_3294_0013, g32p_row02_traceSegment_003_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3321 13 14, g32p_row02_traceSegment_003_3321_0013, g32p_row02_traceSegment_003_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3294 27 27, g32p_row02_traceSegment_003_3294_0027, g32p_row02_traceSegment_003_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3240 54 54, g32p_row02_traceSegment_003_3240_0054, g32p_row02_traceSegment_003_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3348 13 14, g32p_row02_traceSegment_003_3348_0013, g32p_row02_traceSegment_003_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3375 13 14, g32p_row02_traceSegment_003_3375_0013, g32p_row02_traceSegment_003_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3348 27 27, g32p_row02_traceSegment_003_3348_0027, g32p_row02_traceSegment_003_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3402 13 14, g32p_row02_traceSegment_003_3402_0013, g32p_row02_traceSegment_003_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_003 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_003 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_003_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_003 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3429 13 14, g32p_row02_traceSegment_003_3429_0013, g32p_row02_traceSegment_003_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_003 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3402 27 27, g32p_row02_traceSegment_003_3402_0027, g32p_row02_traceSegment_003_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_003 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3348 54 54, g32p_row02_traceSegment_003_3348_0054, g32p_row02_traceSegment_003_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_003 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3240 108 108, g32p_row02_traceSegment_003_3240_0108, g32p_row02_traceSegment_003_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_003_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_003 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 3024 216 216, g32p_row02_traceSegment_003_3024_0216, g32p_row02_traceSegment_003_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_003_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_003 2592 864 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 2592 432 432, g32p_row02_traceSegment_003_2592_0432, g32p_row02_traceSegment_003_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_003_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_003 1728 1728 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 1728 864 864, g32p_row02_traceSegment_003_1728_0864, g32p_row02_traceSegment_003_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_003_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_003 0 3456 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_003 0 1728 1728, g32p_row02_traceSegment_003_0000_1728, g32p_row02_traceSegment_003_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 3 = [8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_003_0000_3456

end HodgeLean.Foundations.Program

end
end
