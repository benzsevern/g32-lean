import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_082 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 82 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_082_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 0 13 14, g32p_row02_traceSegment_082_0000_0013, g32p_row02_traceSegment_082_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 40 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 27 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 27 13 14, g32p_row02_traceSegment_082_0027_0013, g32p_row02_traceSegment_082_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 0 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 0 27 27, g32p_row02_traceSegment_082_0000_0027, g32p_row02_traceSegment_082_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 54 13 14, g32p_row02_traceSegment_082_0054_0013, g32p_row02_traceSegment_082_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 81 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 81 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 81 13 14, g32p_row02_traceSegment_082_0081_0013, g32p_row02_traceSegment_082_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 54 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 54 27 27, g32p_row02_traceSegment_082_0054_0027, g32p_row02_traceSegment_082_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 0 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 0 54 54, g32p_row02_traceSegment_082_0000_0054, g32p_row02_traceSegment_082_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 121 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 108 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 108 13 14, g32p_row02_traceSegment_082_0108_0013, g32p_row02_traceSegment_082_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 135 13 14, g32p_row02_traceSegment_082_0135_0013, g32p_row02_traceSegment_082_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 108 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 108 27 27, g32p_row02_traceSegment_082_0108_0027, g32p_row02_traceSegment_082_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 162 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 175 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 162 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 162 13 14, g32p_row02_traceSegment_082_0162_0013, g32p_row02_traceSegment_082_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 189 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 202 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 189 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 189 13 14, g32p_row02_traceSegment_082_0189_0013, g32p_row02_traceSegment_082_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 162 54 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 162 27 27, g32p_row02_traceSegment_082_0162_0027, g32p_row02_traceSegment_082_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 108 108 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 108 54 54, g32p_row02_traceSegment_082_0108_0054, g32p_row02_traceSegment_082_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 0 216 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 0 108 108, g32p_row02_traceSegment_082_0000_0108, g32p_row02_traceSegment_082_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 229 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 216 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 216 13 14, g32p_row02_traceSegment_082_0216_0013, g32p_row02_traceSegment_082_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 243 13 14, g32p_row02_traceSegment_082_0243_0013, g32p_row02_traceSegment_082_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 216 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 216 27 27, g32p_row02_traceSegment_082_0216_0027, g32p_row02_traceSegment_082_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 270 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 270 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 270 13 14, g32p_row02_traceSegment_082_0270_0013, g32p_row02_traceSegment_082_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 297 13 14, g32p_row02_traceSegment_082_0297_0013, g32p_row02_traceSegment_082_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 270 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 270 27 27, g32p_row02_traceSegment_082_0270_0027, g32p_row02_traceSegment_082_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 216 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 216 54 54, g32p_row02_traceSegment_082_0216_0054, g32p_row02_traceSegment_082_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 324 13 14, g32p_row02_traceSegment_082_0324_0013, g32p_row02_traceSegment_082_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 351 13 14, g32p_row02_traceSegment_082_0351_0013, g32p_row02_traceSegment_082_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 324 27 27, g32p_row02_traceSegment_082_0324_0027, g32p_row02_traceSegment_082_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 378 13 14, g32p_row02_traceSegment_082_0378_0013, g32p_row02_traceSegment_082_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 405 13 14, g32p_row02_traceSegment_082_0405_0013, g32p_row02_traceSegment_082_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 378 27 27, g32p_row02_traceSegment_082_0378_0027, g32p_row02_traceSegment_082_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 324 54 54, g32p_row02_traceSegment_082_0324_0054, g32p_row02_traceSegment_082_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 216 216 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 216 108 108, g32p_row02_traceSegment_082_0216_0108, g32p_row02_traceSegment_082_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_082 0 432 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 0 216 216, g32p_row02_traceSegment_082_0000_0216, g32p_row02_traceSegment_082_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 432 13 14, g32p_row02_traceSegment_082_0432_0013, g32p_row02_traceSegment_082_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 459 13 14, g32p_row02_traceSegment_082_0459_0013, g32p_row02_traceSegment_082_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 432 27 27, g32p_row02_traceSegment_082_0432_0027, g32p_row02_traceSegment_082_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 486 13 14, g32p_row02_traceSegment_082_0486_0013, g32p_row02_traceSegment_082_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 513 13 14, g32p_row02_traceSegment_082_0513_0013, g32p_row02_traceSegment_082_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 486 27 27, g32p_row02_traceSegment_082_0486_0027, g32p_row02_traceSegment_082_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 432 54 54, g32p_row02_traceSegment_082_0432_0054, g32p_row02_traceSegment_082_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 540 13 14, g32p_row02_traceSegment_082_0540_0013, g32p_row02_traceSegment_082_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 567 13 14, g32p_row02_traceSegment_082_0567_0013, g32p_row02_traceSegment_082_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 540 27 27, g32p_row02_traceSegment_082_0540_0027, g32p_row02_traceSegment_082_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 594 13 14, g32p_row02_traceSegment_082_0594_0013, g32p_row02_traceSegment_082_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 621 13 14, g32p_row02_traceSegment_082_0621_0013, g32p_row02_traceSegment_082_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 594 27 27, g32p_row02_traceSegment_082_0594_0027, g32p_row02_traceSegment_082_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 540 54 54, g32p_row02_traceSegment_082_0540_0054, g32p_row02_traceSegment_082_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 432 108 108, g32p_row02_traceSegment_082_0432_0108, g32p_row02_traceSegment_082_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 648 13 14, g32p_row02_traceSegment_082_0648_0013, g32p_row02_traceSegment_082_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 675 13 14, g32p_row02_traceSegment_082_0675_0013, g32p_row02_traceSegment_082_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 648 27 27, g32p_row02_traceSegment_082_0648_0027, g32p_row02_traceSegment_082_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 702 13 14, g32p_row02_traceSegment_082_0702_0013, g32p_row02_traceSegment_082_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 729 13 14, g32p_row02_traceSegment_082_0729_0013, g32p_row02_traceSegment_082_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 702 27 27, g32p_row02_traceSegment_082_0702_0027, g32p_row02_traceSegment_082_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 648 54 54, g32p_row02_traceSegment_082_0648_0054, g32p_row02_traceSegment_082_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 756 13 14, g32p_row02_traceSegment_082_0756_0013, g32p_row02_traceSegment_082_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 783 13 14, g32p_row02_traceSegment_082_0783_0013, g32p_row02_traceSegment_082_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 756 27 27, g32p_row02_traceSegment_082_0756_0027, g32p_row02_traceSegment_082_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 810 13 14, g32p_row02_traceSegment_082_0810_0013, g32p_row02_traceSegment_082_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 837 13 14, g32p_row02_traceSegment_082_0837_0013, g32p_row02_traceSegment_082_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 810 27 27, g32p_row02_traceSegment_082_0810_0027, g32p_row02_traceSegment_082_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 756 54 54, g32p_row02_traceSegment_082_0756_0054, g32p_row02_traceSegment_082_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 648 108 108, g32p_row02_traceSegment_082_0648_0108, g32p_row02_traceSegment_082_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_082 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 432 216 216, g32p_row02_traceSegment_082_0432_0216, g32p_row02_traceSegment_082_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_082 0 864 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 0 432 432, g32p_row02_traceSegment_082_0000_0432, g32p_row02_traceSegment_082_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 864 13 14, g32p_row02_traceSegment_082_0864_0013, g32p_row02_traceSegment_082_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 891 13 14, g32p_row02_traceSegment_082_0891_0013, g32p_row02_traceSegment_082_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 864 27 27, g32p_row02_traceSegment_082_0864_0027, g32p_row02_traceSegment_082_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 918 13 14, g32p_row02_traceSegment_082_0918_0013, g32p_row02_traceSegment_082_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 945 13 14, g32p_row02_traceSegment_082_0945_0013, g32p_row02_traceSegment_082_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 918 27 27, g32p_row02_traceSegment_082_0918_0027, g32p_row02_traceSegment_082_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 864 54 54, g32p_row02_traceSegment_082_0864_0054, g32p_row02_traceSegment_082_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 972 13 14, g32p_row02_traceSegment_082_0972_0013, g32p_row02_traceSegment_082_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 999 13 14, g32p_row02_traceSegment_082_0999_0013, g32p_row02_traceSegment_082_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 972 27 27, g32p_row02_traceSegment_082_0972_0027, g32p_row02_traceSegment_082_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1026 13 14, g32p_row02_traceSegment_082_1026_0013, g32p_row02_traceSegment_082_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1053 13 14, g32p_row02_traceSegment_082_1053_0013, g32p_row02_traceSegment_082_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1026 27 27, g32p_row02_traceSegment_082_1026_0027, g32p_row02_traceSegment_082_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 972 54 54, g32p_row02_traceSegment_082_0972_0054, g32p_row02_traceSegment_082_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 864 108 108, g32p_row02_traceSegment_082_0864_0108, g32p_row02_traceSegment_082_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1080 13 14, g32p_row02_traceSegment_082_1080_0013, g32p_row02_traceSegment_082_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1107 13 14, g32p_row02_traceSegment_082_1107_0013, g32p_row02_traceSegment_082_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1080 27 27, g32p_row02_traceSegment_082_1080_0027, g32p_row02_traceSegment_082_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1134 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1147 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1134 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1134 13 14, g32p_row02_traceSegment_082_1134_0013, g32p_row02_traceSegment_082_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1161 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1161 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1161 13 14, g32p_row02_traceSegment_082_1161_0013, g32p_row02_traceSegment_082_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1134 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1134 27 27, g32p_row02_traceSegment_082_1134_0027, g32p_row02_traceSegment_082_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 1080 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1080 54 54, g32p_row02_traceSegment_082_1080_0054, g32p_row02_traceSegment_082_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1188 13 14, g32p_row02_traceSegment_082_1188_0013, g32p_row02_traceSegment_082_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1215 13 14, g32p_row02_traceSegment_082_1215_0013, g32p_row02_traceSegment_082_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1188 27 27, g32p_row02_traceSegment_082_1188_0027, g32p_row02_traceSegment_082_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1242 13 14, g32p_row02_traceSegment_082_1242_0013, g32p_row02_traceSegment_082_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1269 13 14, g32p_row02_traceSegment_082_1269_0013, g32p_row02_traceSegment_082_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1242 27 27, g32p_row02_traceSegment_082_1242_0027, g32p_row02_traceSegment_082_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1188 54 54, g32p_row02_traceSegment_082_1188_0054, g32p_row02_traceSegment_082_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 1080 216 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1080 108 108, g32p_row02_traceSegment_082_1080_0108, g32p_row02_traceSegment_082_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_082 864 432 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 864 216 216, g32p_row02_traceSegment_082_0864_0216, g32p_row02_traceSegment_082_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1296 13 14, g32p_row02_traceSegment_082_1296_0013, g32p_row02_traceSegment_082_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1323 13 14, g32p_row02_traceSegment_082_1323_0013, g32p_row02_traceSegment_082_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1296 27 27, g32p_row02_traceSegment_082_1296_0027, g32p_row02_traceSegment_082_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1350 13 14, g32p_row02_traceSegment_082_1350_0013, g32p_row02_traceSegment_082_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1377 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1377 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1377 13 14, g32p_row02_traceSegment_082_1377_0013, g32p_row02_traceSegment_082_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1350 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1350 27 27, g32p_row02_traceSegment_082_1350_0027, g32p_row02_traceSegment_082_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 1296 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1296 54 54, g32p_row02_traceSegment_082_1296_0054, g32p_row02_traceSegment_082_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1404 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1417 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1404 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1404 13 14, g32p_row02_traceSegment_082_1404_0013, g32p_row02_traceSegment_082_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1444 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1431 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1431 13 14, g32p_row02_traceSegment_082_1431_0013, g32p_row02_traceSegment_082_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1404 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1404 27 27, g32p_row02_traceSegment_082_1404_0027, g32p_row02_traceSegment_082_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1458 13 14, g32p_row02_traceSegment_082_1458_0013, g32p_row02_traceSegment_082_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1485 13 14, g32p_row02_traceSegment_082_1485_0013, g32p_row02_traceSegment_082_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1458 27 27, g32p_row02_traceSegment_082_1458_0027, g32p_row02_traceSegment_082_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 1404 108 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1404 54 54, g32p_row02_traceSegment_082_1404_0054, g32p_row02_traceSegment_082_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 1296 216 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1296 108 108, g32p_row02_traceSegment_082_1296_0108, g32p_row02_traceSegment_082_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1512 13 14, g32p_row02_traceSegment_082_1512_0013, g32p_row02_traceSegment_082_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1539 13 14, g32p_row02_traceSegment_082_1539_0013, g32p_row02_traceSegment_082_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1512 27 27, g32p_row02_traceSegment_082_1512_0027, g32p_row02_traceSegment_082_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1566 13 14, g32p_row02_traceSegment_082_1566_0013, g32p_row02_traceSegment_082_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1593 13 14, g32p_row02_traceSegment_082_1593_0013, g32p_row02_traceSegment_082_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1566 27 27, g32p_row02_traceSegment_082_1566_0027, g32p_row02_traceSegment_082_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1512 54 54, g32p_row02_traceSegment_082_1512_0054, g32p_row02_traceSegment_082_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1633 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1620 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1620 13 14, g32p_row02_traceSegment_082_1620_0013, g32p_row02_traceSegment_082_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1647 13 14, g32p_row02_traceSegment_082_1647_0013, g32p_row02_traceSegment_082_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1620 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1620 27 27, g32p_row02_traceSegment_082_1620_0027, g32p_row02_traceSegment_082_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1674 13 14, g32p_row02_traceSegment_082_1674_0013, g32p_row02_traceSegment_082_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1701 13 14, g32p_row02_traceSegment_082_1701_0013, g32p_row02_traceSegment_082_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1674 27 27, g32p_row02_traceSegment_082_1674_0027, g32p_row02_traceSegment_082_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 1620 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1620 54 54, g32p_row02_traceSegment_082_1620_0054, g32p_row02_traceSegment_082_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 1512 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1512 108 108, g32p_row02_traceSegment_082_1512_0108, g32p_row02_traceSegment_082_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_082 1296 432 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1296 216 216, g32p_row02_traceSegment_082_1296_0216, g32p_row02_traceSegment_082_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_082 864 864 = [0, 0, 1, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 864 432 432, g32p_row02_traceSegment_082_0864_0432, g32p_row02_traceSegment_082_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_082 0 1728 = [0, 0, 1, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 0 864 864, g32p_row02_traceSegment_082_0000_0864, g32p_row02_traceSegment_082_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1728 13 14, g32p_row02_traceSegment_082_1728_0013, g32p_row02_traceSegment_082_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1755 13 14, g32p_row02_traceSegment_082_1755_0013, g32p_row02_traceSegment_082_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1728 27 27, g32p_row02_traceSegment_082_1728_0027, g32p_row02_traceSegment_082_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1782 13 14, g32p_row02_traceSegment_082_1782_0013, g32p_row02_traceSegment_082_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1809 13 14, g32p_row02_traceSegment_082_1809_0013, g32p_row02_traceSegment_082_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1782 27 27, g32p_row02_traceSegment_082_1782_0027, g32p_row02_traceSegment_082_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1728 54 54, g32p_row02_traceSegment_082_1728_0054, g32p_row02_traceSegment_082_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1836 13 14, g32p_row02_traceSegment_082_1836_0013, g32p_row02_traceSegment_082_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1863 13 14, g32p_row02_traceSegment_082_1863_0013, g32p_row02_traceSegment_082_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1836 27 27, g32p_row02_traceSegment_082_1836_0027, g32p_row02_traceSegment_082_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1890 13 14, g32p_row02_traceSegment_082_1890_0013, g32p_row02_traceSegment_082_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1917 13 14, g32p_row02_traceSegment_082_1917_0013, g32p_row02_traceSegment_082_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1890 27 27, g32p_row02_traceSegment_082_1890_0027, g32p_row02_traceSegment_082_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1836 54 54, g32p_row02_traceSegment_082_1836_0054, g32p_row02_traceSegment_082_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1728 108 108, g32p_row02_traceSegment_082_1728_0108, g32p_row02_traceSegment_082_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1944 13 14, g32p_row02_traceSegment_082_1944_0013, g32p_row02_traceSegment_082_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1971 13 14, g32p_row02_traceSegment_082_1971_0013, g32p_row02_traceSegment_082_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1944 27 27, g32p_row02_traceSegment_082_1944_0027, g32p_row02_traceSegment_082_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1998 13 14, g32p_row02_traceSegment_082_1998_0013, g32p_row02_traceSegment_082_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2025 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2025 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2025 13 14, g32p_row02_traceSegment_082_2025_0013, g32p_row02_traceSegment_082_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 1998 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1998 27 27, g32p_row02_traceSegment_082_1998_0027, g32p_row02_traceSegment_082_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 1944 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1944 54 54, g32p_row02_traceSegment_082_1944_0054, g32p_row02_traceSegment_082_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2052 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2065 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2052 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2052 13 14, g32p_row02_traceSegment_082_2052_0013, g32p_row02_traceSegment_082_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2079 13 14, g32p_row02_traceSegment_082_2079_0013, g32p_row02_traceSegment_082_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2052 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2052 27 27, g32p_row02_traceSegment_082_2052_0027, g32p_row02_traceSegment_082_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2106 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2106 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2106 13 14, g32p_row02_traceSegment_082_2106_0013, g32p_row02_traceSegment_082_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2133 13 14, g32p_row02_traceSegment_082_2133_0013, g32p_row02_traceSegment_082_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2106 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2106 27 27, g32p_row02_traceSegment_082_2106_0027, g32p_row02_traceSegment_082_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 2052 108 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2052 54 54, g32p_row02_traceSegment_082_2052_0054, g32p_row02_traceSegment_082_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 1944 216 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1944 108 108, g32p_row02_traceSegment_082_1944_0108, g32p_row02_traceSegment_082_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_082 1728 432 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1728 216 216, g32p_row02_traceSegment_082_1728_0216, g32p_row02_traceSegment_082_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2160 13 14, g32p_row02_traceSegment_082_2160_0013, g32p_row02_traceSegment_082_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2187 13 14, g32p_row02_traceSegment_082_2187_0013, g32p_row02_traceSegment_082_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2160 27 27, g32p_row02_traceSegment_082_2160_0027, g32p_row02_traceSegment_082_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2214 13 14, g32p_row02_traceSegment_082_2214_0013, g32p_row02_traceSegment_082_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2241 13 14, g32p_row02_traceSegment_082_2241_0013, g32p_row02_traceSegment_082_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2214 27 27, g32p_row02_traceSegment_082_2214_0027, g32p_row02_traceSegment_082_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2160 54 54, g32p_row02_traceSegment_082_2160_0054, g32p_row02_traceSegment_082_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2268 13 14, g32p_row02_traceSegment_082_2268_0013, g32p_row02_traceSegment_082_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2295 13 14, g32p_row02_traceSegment_082_2295_0013, g32p_row02_traceSegment_082_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2268 27 27, g32p_row02_traceSegment_082_2268_0027, g32p_row02_traceSegment_082_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2322 13 14, g32p_row02_traceSegment_082_2322_0013, g32p_row02_traceSegment_082_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2349 13 14, g32p_row02_traceSegment_082_2349_0013, g32p_row02_traceSegment_082_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2322 27 27, g32p_row02_traceSegment_082_2322_0027, g32p_row02_traceSegment_082_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2268 54 54, g32p_row02_traceSegment_082_2268_0054, g32p_row02_traceSegment_082_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2160 108 108, g32p_row02_traceSegment_082_2160_0108, g32p_row02_traceSegment_082_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2376 13 14, g32p_row02_traceSegment_082_2376_0013, g32p_row02_traceSegment_082_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2403 13 14, g32p_row02_traceSegment_082_2403_0013, g32p_row02_traceSegment_082_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2376 27 27, g32p_row02_traceSegment_082_2376_0027, g32p_row02_traceSegment_082_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2430 13 14, g32p_row02_traceSegment_082_2430_0013, g32p_row02_traceSegment_082_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2457 13 14, g32p_row02_traceSegment_082_2457_0013, g32p_row02_traceSegment_082_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2430 27 27, g32p_row02_traceSegment_082_2430_0027, g32p_row02_traceSegment_082_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2376 54 54, g32p_row02_traceSegment_082_2376_0054, g32p_row02_traceSegment_082_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2484 13 14, g32p_row02_traceSegment_082_2484_0013, g32p_row02_traceSegment_082_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2511 13 14, g32p_row02_traceSegment_082_2511_0013, g32p_row02_traceSegment_082_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2484 27 27, g32p_row02_traceSegment_082_2484_0027, g32p_row02_traceSegment_082_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2538 13 14, g32p_row02_traceSegment_082_2538_0013, g32p_row02_traceSegment_082_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2565 13 14, g32p_row02_traceSegment_082_2565_0013, g32p_row02_traceSegment_082_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2538 27 27, g32p_row02_traceSegment_082_2538_0027, g32p_row02_traceSegment_082_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2484 54 54, g32p_row02_traceSegment_082_2484_0054, g32p_row02_traceSegment_082_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2376 108 108, g32p_row02_traceSegment_082_2376_0108, g32p_row02_traceSegment_082_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_082 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2160 216 216, g32p_row02_traceSegment_082_2160_0216, g32p_row02_traceSegment_082_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_082 1728 864 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1728 432 432, g32p_row02_traceSegment_082_1728_0432, g32p_row02_traceSegment_082_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2592 13 14, g32p_row02_traceSegment_082_2592_0013, g32p_row02_traceSegment_082_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2619 13 14, g32p_row02_traceSegment_082_2619_0013, g32p_row02_traceSegment_082_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2592 27 27, g32p_row02_traceSegment_082_2592_0027, g32p_row02_traceSegment_082_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2646 13 14, g32p_row02_traceSegment_082_2646_0013, g32p_row02_traceSegment_082_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2673 13 14, g32p_row02_traceSegment_082_2673_0013, g32p_row02_traceSegment_082_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2646 27 27, g32p_row02_traceSegment_082_2646_0027, g32p_row02_traceSegment_082_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2592 54 54, g32p_row02_traceSegment_082_2592_0054, g32p_row02_traceSegment_082_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2700 13 14, g32p_row02_traceSegment_082_2700_0013, g32p_row02_traceSegment_082_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2727 13 14, g32p_row02_traceSegment_082_2727_0013, g32p_row02_traceSegment_082_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2700 27 27, g32p_row02_traceSegment_082_2700_0027, g32p_row02_traceSegment_082_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2754 13 14, g32p_row02_traceSegment_082_2754_0013, g32p_row02_traceSegment_082_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2781 13 14, g32p_row02_traceSegment_082_2781_0013, g32p_row02_traceSegment_082_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2754 27 27, g32p_row02_traceSegment_082_2754_0027, g32p_row02_traceSegment_082_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2700 54 54, g32p_row02_traceSegment_082_2700_0054, g32p_row02_traceSegment_082_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2592 108 108, g32p_row02_traceSegment_082_2592_0108, g32p_row02_traceSegment_082_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2808 13 14, g32p_row02_traceSegment_082_2808_0013, g32p_row02_traceSegment_082_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2835 13 14, g32p_row02_traceSegment_082_2835_0013, g32p_row02_traceSegment_082_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2808 27 27, g32p_row02_traceSegment_082_2808_0027, g32p_row02_traceSegment_082_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2862 13 14, g32p_row02_traceSegment_082_2862_0013, g32p_row02_traceSegment_082_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2889 13 14, g32p_row02_traceSegment_082_2889_0013, g32p_row02_traceSegment_082_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2862 27 27, g32p_row02_traceSegment_082_2862_0027, g32p_row02_traceSegment_082_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2808 54 54, g32p_row02_traceSegment_082_2808_0054, g32p_row02_traceSegment_082_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2916 13 14, g32p_row02_traceSegment_082_2916_0013, g32p_row02_traceSegment_082_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2943 13 14, g32p_row02_traceSegment_082_2943_0013, g32p_row02_traceSegment_082_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2916 27 27, g32p_row02_traceSegment_082_2916_0027, g32p_row02_traceSegment_082_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2970 13 14, g32p_row02_traceSegment_082_2970_0013, g32p_row02_traceSegment_082_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2997 13 14, g32p_row02_traceSegment_082_2997_0013, g32p_row02_traceSegment_082_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2970 27 27, g32p_row02_traceSegment_082_2970_0027, g32p_row02_traceSegment_082_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2916 54 54, g32p_row02_traceSegment_082_2916_0054, g32p_row02_traceSegment_082_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2808 108 108, g32p_row02_traceSegment_082_2808_0108, g32p_row02_traceSegment_082_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_082 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2592 216 216, g32p_row02_traceSegment_082_2592_0216, g32p_row02_traceSegment_082_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3024 13 14, g32p_row02_traceSegment_082_3024_0013, g32p_row02_traceSegment_082_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3051 13 14, g32p_row02_traceSegment_082_3051_0013, g32p_row02_traceSegment_082_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3024 27 27, g32p_row02_traceSegment_082_3024_0027, g32p_row02_traceSegment_082_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3078 13 14, g32p_row02_traceSegment_082_3078_0013, g32p_row02_traceSegment_082_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3105 13 14, g32p_row02_traceSegment_082_3105_0013, g32p_row02_traceSegment_082_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3078 27 27, g32p_row02_traceSegment_082_3078_0027, g32p_row02_traceSegment_082_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3024 54 54, g32p_row02_traceSegment_082_3024_0054, g32p_row02_traceSegment_082_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3132 13 14, g32p_row02_traceSegment_082_3132_0013, g32p_row02_traceSegment_082_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3159 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3159 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3159 13 14, g32p_row02_traceSegment_082_3159_0013, g32p_row02_traceSegment_082_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 3132 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3132 27 27, g32p_row02_traceSegment_082_3132_0027, g32p_row02_traceSegment_082_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3186 13 14, g32p_row02_traceSegment_082_3186_0013, g32p_row02_traceSegment_082_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3213 13 14, g32p_row02_traceSegment_082_3213_0013, g32p_row02_traceSegment_082_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3186 27 27, g32p_row02_traceSegment_082_3186_0027, g32p_row02_traceSegment_082_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 3132 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3132 54 54, g32p_row02_traceSegment_082_3132_0054, g32p_row02_traceSegment_082_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 3024 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3024 108 108, g32p_row02_traceSegment_082_3024_0108, g32p_row02_traceSegment_082_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3240 13 14, g32p_row02_traceSegment_082_3240_0013, g32p_row02_traceSegment_082_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3267 13 14, g32p_row02_traceSegment_082_3267_0013, g32p_row02_traceSegment_082_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3240 27 27, g32p_row02_traceSegment_082_3240_0027, g32p_row02_traceSegment_082_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3294 13 14, g32p_row02_traceSegment_082_3294_0013, g32p_row02_traceSegment_082_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3321 13 14, g32p_row02_traceSegment_082_3321_0013, g32p_row02_traceSegment_082_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3294 27 27, g32p_row02_traceSegment_082_3294_0027, g32p_row02_traceSegment_082_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3240 54 54, g32p_row02_traceSegment_082_3240_0054, g32p_row02_traceSegment_082_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3348 13 14, g32p_row02_traceSegment_082_3348_0013, g32p_row02_traceSegment_082_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3375 13 14, g32p_row02_traceSegment_082_3375_0013, g32p_row02_traceSegment_082_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3348 27 27, g32p_row02_traceSegment_082_3348_0027, g32p_row02_traceSegment_082_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3402 13 14, g32p_row02_traceSegment_082_3402_0013, g32p_row02_traceSegment_082_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_082 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_082 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_082_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_082 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3429 13 14, g32p_row02_traceSegment_082_3429_0013, g32p_row02_traceSegment_082_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_082 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3402 27 27, g32p_row02_traceSegment_082_3402_0027, g32p_row02_traceSegment_082_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_082 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3348 54 54, g32p_row02_traceSegment_082_3348_0054, g32p_row02_traceSegment_082_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_082 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3240 108 108, g32p_row02_traceSegment_082_3240_0108, g32p_row02_traceSegment_082_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_082_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_082 3024 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 3024 216 216, g32p_row02_traceSegment_082_3024_0216, g32p_row02_traceSegment_082_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_082_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_082 2592 864 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 2592 432 432, g32p_row02_traceSegment_082_2592_0432, g32p_row02_traceSegment_082_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_082_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_082 1728 1728 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 1728 864 864, g32p_row02_traceSegment_082_1728_0864, g32p_row02_traceSegment_082_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_082_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_082 0 3456 = [0, 0, 2, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_082 0 1728 1728, g32p_row02_traceSegment_082_0000_1728, g32p_row02_traceSegment_082_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 82 = [0, 0, 2, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_082_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_083 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 83 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_083_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 0 13 14, g32p_row02_traceSegment_083_0000_0013, g32p_row02_traceSegment_083_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 27 13 14, g32p_row02_traceSegment_083_0027_0013, g32p_row02_traceSegment_083_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 0 27 27, g32p_row02_traceSegment_083_0000_0027, g32p_row02_traceSegment_083_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 54 13 14, g32p_row02_traceSegment_083_0054_0013, g32p_row02_traceSegment_083_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 81 13 14, g32p_row02_traceSegment_083_0081_0013, g32p_row02_traceSegment_083_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 54 27 27, g32p_row02_traceSegment_083_0054_0027, g32p_row02_traceSegment_083_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 0 54 54, g32p_row02_traceSegment_083_0000_0054, g32p_row02_traceSegment_083_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 108 13 14, g32p_row02_traceSegment_083_0108_0013, g32p_row02_traceSegment_083_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 135 13 14, g32p_row02_traceSegment_083_0135_0013, g32p_row02_traceSegment_083_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 108 27 27, g32p_row02_traceSegment_083_0108_0027, g32p_row02_traceSegment_083_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 162 13 14, g32p_row02_traceSegment_083_0162_0013, g32p_row02_traceSegment_083_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 189 13 14, g32p_row02_traceSegment_083_0189_0013, g32p_row02_traceSegment_083_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 162 27 27, g32p_row02_traceSegment_083_0162_0027, g32p_row02_traceSegment_083_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 108 54 54, g32p_row02_traceSegment_083_0108_0054, g32p_row02_traceSegment_083_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 0 108 108, g32p_row02_traceSegment_083_0000_0108, g32p_row02_traceSegment_083_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 216 13 14, g32p_row02_traceSegment_083_0216_0013, g32p_row02_traceSegment_083_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 243 13 14, g32p_row02_traceSegment_083_0243_0013, g32p_row02_traceSegment_083_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 216 27 27, g32p_row02_traceSegment_083_0216_0027, g32p_row02_traceSegment_083_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 270 13 14, g32p_row02_traceSegment_083_0270_0013, g32p_row02_traceSegment_083_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 297 13 14, g32p_row02_traceSegment_083_0297_0013, g32p_row02_traceSegment_083_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 270 27 27, g32p_row02_traceSegment_083_0270_0027, g32p_row02_traceSegment_083_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 216 54 54, g32p_row02_traceSegment_083_0216_0054, g32p_row02_traceSegment_083_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 324 13 14, g32p_row02_traceSegment_083_0324_0013, g32p_row02_traceSegment_083_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 351 13 14, g32p_row02_traceSegment_083_0351_0013, g32p_row02_traceSegment_083_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 324 27 27, g32p_row02_traceSegment_083_0324_0027, g32p_row02_traceSegment_083_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 378 13 14, g32p_row02_traceSegment_083_0378_0013, g32p_row02_traceSegment_083_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 405 13 14, g32p_row02_traceSegment_083_0405_0013, g32p_row02_traceSegment_083_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 378 27 27, g32p_row02_traceSegment_083_0378_0027, g32p_row02_traceSegment_083_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 324 54 54, g32p_row02_traceSegment_083_0324_0054, g32p_row02_traceSegment_083_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 216 108 108, g32p_row02_traceSegment_083_0216_0108, g32p_row02_traceSegment_083_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_083 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 0 216 216, g32p_row02_traceSegment_083_0000_0216, g32p_row02_traceSegment_083_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 432 13 14, g32p_row02_traceSegment_083_0432_0013, g32p_row02_traceSegment_083_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 459 13 14, g32p_row02_traceSegment_083_0459_0013, g32p_row02_traceSegment_083_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 432 27 27, g32p_row02_traceSegment_083_0432_0027, g32p_row02_traceSegment_083_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 486 13 14, g32p_row02_traceSegment_083_0486_0013, g32p_row02_traceSegment_083_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 513 13 14, g32p_row02_traceSegment_083_0513_0013, g32p_row02_traceSegment_083_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 486 27 27, g32p_row02_traceSegment_083_0486_0027, g32p_row02_traceSegment_083_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 432 54 54, g32p_row02_traceSegment_083_0432_0054, g32p_row02_traceSegment_083_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 540 13 14, g32p_row02_traceSegment_083_0540_0013, g32p_row02_traceSegment_083_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 567 13 14, g32p_row02_traceSegment_083_0567_0013, g32p_row02_traceSegment_083_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 540 27 27, g32p_row02_traceSegment_083_0540_0027, g32p_row02_traceSegment_083_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 594 13 14, g32p_row02_traceSegment_083_0594_0013, g32p_row02_traceSegment_083_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 621 13 14, g32p_row02_traceSegment_083_0621_0013, g32p_row02_traceSegment_083_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 594 27 27, g32p_row02_traceSegment_083_0594_0027, g32p_row02_traceSegment_083_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 540 54 54, g32p_row02_traceSegment_083_0540_0054, g32p_row02_traceSegment_083_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 432 108 108, g32p_row02_traceSegment_083_0432_0108, g32p_row02_traceSegment_083_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 648 13 14, g32p_row02_traceSegment_083_0648_0013, g32p_row02_traceSegment_083_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 675 13 14, g32p_row02_traceSegment_083_0675_0013, g32p_row02_traceSegment_083_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 648 27 27, g32p_row02_traceSegment_083_0648_0027, g32p_row02_traceSegment_083_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 702 13 14, g32p_row02_traceSegment_083_0702_0013, g32p_row02_traceSegment_083_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 729 13 14, g32p_row02_traceSegment_083_0729_0013, g32p_row02_traceSegment_083_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 702 27 27, g32p_row02_traceSegment_083_0702_0027, g32p_row02_traceSegment_083_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 648 54 54, g32p_row02_traceSegment_083_0648_0054, g32p_row02_traceSegment_083_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 756 13 14, g32p_row02_traceSegment_083_0756_0013, g32p_row02_traceSegment_083_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 783 13 14, g32p_row02_traceSegment_083_0783_0013, g32p_row02_traceSegment_083_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 756 27 27, g32p_row02_traceSegment_083_0756_0027, g32p_row02_traceSegment_083_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 810 13 14, g32p_row02_traceSegment_083_0810_0013, g32p_row02_traceSegment_083_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 837 13 14, g32p_row02_traceSegment_083_0837_0013, g32p_row02_traceSegment_083_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 810 27 27, g32p_row02_traceSegment_083_0810_0027, g32p_row02_traceSegment_083_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 756 54 54, g32p_row02_traceSegment_083_0756_0054, g32p_row02_traceSegment_083_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 648 108 108, g32p_row02_traceSegment_083_0648_0108, g32p_row02_traceSegment_083_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_083 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 432 216 216, g32p_row02_traceSegment_083_0432_0216, g32p_row02_traceSegment_083_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_083 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 0 432 432, g32p_row02_traceSegment_083_0000_0432, g32p_row02_traceSegment_083_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 864 13 14, g32p_row02_traceSegment_083_0864_0013, g32p_row02_traceSegment_083_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 891 13 14, g32p_row02_traceSegment_083_0891_0013, g32p_row02_traceSegment_083_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 864 27 27, g32p_row02_traceSegment_083_0864_0027, g32p_row02_traceSegment_083_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 918 13 14, g32p_row02_traceSegment_083_0918_0013, g32p_row02_traceSegment_083_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 945 13 14, g32p_row02_traceSegment_083_0945_0013, g32p_row02_traceSegment_083_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 918 27 27, g32p_row02_traceSegment_083_0918_0027, g32p_row02_traceSegment_083_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 864 54 54, g32p_row02_traceSegment_083_0864_0054, g32p_row02_traceSegment_083_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 972 13 14, g32p_row02_traceSegment_083_0972_0013, g32p_row02_traceSegment_083_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 999 13 14, g32p_row02_traceSegment_083_0999_0013, g32p_row02_traceSegment_083_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 972 27 27, g32p_row02_traceSegment_083_0972_0027, g32p_row02_traceSegment_083_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1026 13 14, g32p_row02_traceSegment_083_1026_0013, g32p_row02_traceSegment_083_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1053 13 14, g32p_row02_traceSegment_083_1053_0013, g32p_row02_traceSegment_083_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1026 27 27, g32p_row02_traceSegment_083_1026_0027, g32p_row02_traceSegment_083_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 972 54 54, g32p_row02_traceSegment_083_0972_0054, g32p_row02_traceSegment_083_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 864 108 108, g32p_row02_traceSegment_083_0864_0108, g32p_row02_traceSegment_083_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1080 13 14, g32p_row02_traceSegment_083_1080_0013, g32p_row02_traceSegment_083_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1107 13 14, g32p_row02_traceSegment_083_1107_0013, g32p_row02_traceSegment_083_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1080 27 27, g32p_row02_traceSegment_083_1080_0027, g32p_row02_traceSegment_083_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1134 13 14, g32p_row02_traceSegment_083_1134_0013, g32p_row02_traceSegment_083_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1161 13 14, g32p_row02_traceSegment_083_1161_0013, g32p_row02_traceSegment_083_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1134 27 27, g32p_row02_traceSegment_083_1134_0027, g32p_row02_traceSegment_083_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1080 54 54, g32p_row02_traceSegment_083_1080_0054, g32p_row02_traceSegment_083_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1188 13 14, g32p_row02_traceSegment_083_1188_0013, g32p_row02_traceSegment_083_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1215 13 14, g32p_row02_traceSegment_083_1215_0013, g32p_row02_traceSegment_083_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1188 27 27, g32p_row02_traceSegment_083_1188_0027, g32p_row02_traceSegment_083_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1242 13 14, g32p_row02_traceSegment_083_1242_0013, g32p_row02_traceSegment_083_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1269 13 14, g32p_row02_traceSegment_083_1269_0013, g32p_row02_traceSegment_083_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1242 27 27, g32p_row02_traceSegment_083_1242_0027, g32p_row02_traceSegment_083_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1188 54 54, g32p_row02_traceSegment_083_1188_0054, g32p_row02_traceSegment_083_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1080 108 108, g32p_row02_traceSegment_083_1080_0108, g32p_row02_traceSegment_083_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_083 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 864 216 216, g32p_row02_traceSegment_083_0864_0216, g32p_row02_traceSegment_083_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1296 13 14, g32p_row02_traceSegment_083_1296_0013, g32p_row02_traceSegment_083_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1323 13 14, g32p_row02_traceSegment_083_1323_0013, g32p_row02_traceSegment_083_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1296 27 27, g32p_row02_traceSegment_083_1296_0027, g32p_row02_traceSegment_083_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1350 13 14, g32p_row02_traceSegment_083_1350_0013, g32p_row02_traceSegment_083_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1377 13 14, g32p_row02_traceSegment_083_1377_0013, g32p_row02_traceSegment_083_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1350 27 27, g32p_row02_traceSegment_083_1350_0027, g32p_row02_traceSegment_083_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1296 54 54, g32p_row02_traceSegment_083_1296_0054, g32p_row02_traceSegment_083_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1404 13 14, g32p_row02_traceSegment_083_1404_0013, g32p_row02_traceSegment_083_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1431 13 14, g32p_row02_traceSegment_083_1431_0013, g32p_row02_traceSegment_083_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1404 27 27, g32p_row02_traceSegment_083_1404_0027, g32p_row02_traceSegment_083_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1458 13 14, g32p_row02_traceSegment_083_1458_0013, g32p_row02_traceSegment_083_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1485 13 14, g32p_row02_traceSegment_083_1485_0013, g32p_row02_traceSegment_083_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1458 27 27, g32p_row02_traceSegment_083_1458_0027, g32p_row02_traceSegment_083_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1404 54 54, g32p_row02_traceSegment_083_1404_0054, g32p_row02_traceSegment_083_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1296 108 108, g32p_row02_traceSegment_083_1296_0108, g32p_row02_traceSegment_083_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1512 13 14, g32p_row02_traceSegment_083_1512_0013, g32p_row02_traceSegment_083_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1539 13 14, g32p_row02_traceSegment_083_1539_0013, g32p_row02_traceSegment_083_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1512 27 27, g32p_row02_traceSegment_083_1512_0027, g32p_row02_traceSegment_083_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1566 13 14, g32p_row02_traceSegment_083_1566_0013, g32p_row02_traceSegment_083_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1593 13 14, g32p_row02_traceSegment_083_1593_0013, g32p_row02_traceSegment_083_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1566 27 27, g32p_row02_traceSegment_083_1566_0027, g32p_row02_traceSegment_083_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1512 54 54, g32p_row02_traceSegment_083_1512_0054, g32p_row02_traceSegment_083_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1620 13 14, g32p_row02_traceSegment_083_1620_0013, g32p_row02_traceSegment_083_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1647 13 14, g32p_row02_traceSegment_083_1647_0013, g32p_row02_traceSegment_083_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1620 27 27, g32p_row02_traceSegment_083_1620_0027, g32p_row02_traceSegment_083_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1674 13 14, g32p_row02_traceSegment_083_1674_0013, g32p_row02_traceSegment_083_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1701 13 14, g32p_row02_traceSegment_083_1701_0013, g32p_row02_traceSegment_083_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1674 27 27, g32p_row02_traceSegment_083_1674_0027, g32p_row02_traceSegment_083_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1620 54 54, g32p_row02_traceSegment_083_1620_0054, g32p_row02_traceSegment_083_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1512 108 108, g32p_row02_traceSegment_083_1512_0108, g32p_row02_traceSegment_083_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_083 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1296 216 216, g32p_row02_traceSegment_083_1296_0216, g32p_row02_traceSegment_083_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_083 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 864 432 432, g32p_row02_traceSegment_083_0864_0432, g32p_row02_traceSegment_083_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_083 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 0 864 864, g32p_row02_traceSegment_083_0000_0864, g32p_row02_traceSegment_083_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1728 13 14, g32p_row02_traceSegment_083_1728_0013, g32p_row02_traceSegment_083_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1755 13 14, g32p_row02_traceSegment_083_1755_0013, g32p_row02_traceSegment_083_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1728 27 27, g32p_row02_traceSegment_083_1728_0027, g32p_row02_traceSegment_083_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1782 13 14, g32p_row02_traceSegment_083_1782_0013, g32p_row02_traceSegment_083_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1809 13 14, g32p_row02_traceSegment_083_1809_0013, g32p_row02_traceSegment_083_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1782 27 27, g32p_row02_traceSegment_083_1782_0027, g32p_row02_traceSegment_083_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1728 54 54, g32p_row02_traceSegment_083_1728_0054, g32p_row02_traceSegment_083_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1836 13 14, g32p_row02_traceSegment_083_1836_0013, g32p_row02_traceSegment_083_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1863 13 14, g32p_row02_traceSegment_083_1863_0013, g32p_row02_traceSegment_083_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1836 27 27, g32p_row02_traceSegment_083_1836_0027, g32p_row02_traceSegment_083_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1890 13 14, g32p_row02_traceSegment_083_1890_0013, g32p_row02_traceSegment_083_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1917 13 14, g32p_row02_traceSegment_083_1917_0013, g32p_row02_traceSegment_083_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1890 27 27, g32p_row02_traceSegment_083_1890_0027, g32p_row02_traceSegment_083_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1836 54 54, g32p_row02_traceSegment_083_1836_0054, g32p_row02_traceSegment_083_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1728 108 108, g32p_row02_traceSegment_083_1728_0108, g32p_row02_traceSegment_083_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1944 13 14, g32p_row02_traceSegment_083_1944_0013, g32p_row02_traceSegment_083_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1971 13 14, g32p_row02_traceSegment_083_1971_0013, g32p_row02_traceSegment_083_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1944 27 27, g32p_row02_traceSegment_083_1944_0027, g32p_row02_traceSegment_083_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1998 13 14, g32p_row02_traceSegment_083_1998_0013, g32p_row02_traceSegment_083_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2025 13 14, g32p_row02_traceSegment_083_2025_0013, g32p_row02_traceSegment_083_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1998 27 27, g32p_row02_traceSegment_083_1998_0027, g32p_row02_traceSegment_083_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1944 54 54, g32p_row02_traceSegment_083_1944_0054, g32p_row02_traceSegment_083_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2052 13 14, g32p_row02_traceSegment_083_2052_0013, g32p_row02_traceSegment_083_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2079 13 14, g32p_row02_traceSegment_083_2079_0013, g32p_row02_traceSegment_083_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2052 27 27, g32p_row02_traceSegment_083_2052_0027, g32p_row02_traceSegment_083_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2106 13 14, g32p_row02_traceSegment_083_2106_0013, g32p_row02_traceSegment_083_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2133 13 14, g32p_row02_traceSegment_083_2133_0013, g32p_row02_traceSegment_083_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2106 27 27, g32p_row02_traceSegment_083_2106_0027, g32p_row02_traceSegment_083_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2052 54 54, g32p_row02_traceSegment_083_2052_0054, g32p_row02_traceSegment_083_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1944 108 108, g32p_row02_traceSegment_083_1944_0108, g32p_row02_traceSegment_083_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_083 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1728 216 216, g32p_row02_traceSegment_083_1728_0216, g32p_row02_traceSegment_083_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2160 13 14, g32p_row02_traceSegment_083_2160_0013, g32p_row02_traceSegment_083_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2187 13 14, g32p_row02_traceSegment_083_2187_0013, g32p_row02_traceSegment_083_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2160 27 27, g32p_row02_traceSegment_083_2160_0027, g32p_row02_traceSegment_083_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2214 13 14, g32p_row02_traceSegment_083_2214_0013, g32p_row02_traceSegment_083_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2241 13 14, g32p_row02_traceSegment_083_2241_0013, g32p_row02_traceSegment_083_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2214 27 27, g32p_row02_traceSegment_083_2214_0027, g32p_row02_traceSegment_083_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2160 54 54, g32p_row02_traceSegment_083_2160_0054, g32p_row02_traceSegment_083_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2268 13 14, g32p_row02_traceSegment_083_2268_0013, g32p_row02_traceSegment_083_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2295 13 14, g32p_row02_traceSegment_083_2295_0013, g32p_row02_traceSegment_083_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2268 27 27, g32p_row02_traceSegment_083_2268_0027, g32p_row02_traceSegment_083_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2322 13 14, g32p_row02_traceSegment_083_2322_0013, g32p_row02_traceSegment_083_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2349 13 14, g32p_row02_traceSegment_083_2349_0013, g32p_row02_traceSegment_083_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2322 27 27, g32p_row02_traceSegment_083_2322_0027, g32p_row02_traceSegment_083_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2268 54 54, g32p_row02_traceSegment_083_2268_0054, g32p_row02_traceSegment_083_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2160 108 108, g32p_row02_traceSegment_083_2160_0108, g32p_row02_traceSegment_083_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2376 13 14, g32p_row02_traceSegment_083_2376_0013, g32p_row02_traceSegment_083_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2403 13 14, g32p_row02_traceSegment_083_2403_0013, g32p_row02_traceSegment_083_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2376 27 27, g32p_row02_traceSegment_083_2376_0027, g32p_row02_traceSegment_083_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2430 13 14, g32p_row02_traceSegment_083_2430_0013, g32p_row02_traceSegment_083_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2457 13 14, g32p_row02_traceSegment_083_2457_0013, g32p_row02_traceSegment_083_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2430 27 27, g32p_row02_traceSegment_083_2430_0027, g32p_row02_traceSegment_083_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2376 54 54, g32p_row02_traceSegment_083_2376_0054, g32p_row02_traceSegment_083_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2484 13 14, g32p_row02_traceSegment_083_2484_0013, g32p_row02_traceSegment_083_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2511 13 14, g32p_row02_traceSegment_083_2511_0013, g32p_row02_traceSegment_083_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2484 27 27, g32p_row02_traceSegment_083_2484_0027, g32p_row02_traceSegment_083_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2538 13 14, g32p_row02_traceSegment_083_2538_0013, g32p_row02_traceSegment_083_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2565 13 14, g32p_row02_traceSegment_083_2565_0013, g32p_row02_traceSegment_083_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2538 27 27, g32p_row02_traceSegment_083_2538_0027, g32p_row02_traceSegment_083_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2484 54 54, g32p_row02_traceSegment_083_2484_0054, g32p_row02_traceSegment_083_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2376 108 108, g32p_row02_traceSegment_083_2376_0108, g32p_row02_traceSegment_083_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_083 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2160 216 216, g32p_row02_traceSegment_083_2160_0216, g32p_row02_traceSegment_083_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_083 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1728 432 432, g32p_row02_traceSegment_083_1728_0432, g32p_row02_traceSegment_083_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2592 13 14, g32p_row02_traceSegment_083_2592_0013, g32p_row02_traceSegment_083_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2619 13 14, g32p_row02_traceSegment_083_2619_0013, g32p_row02_traceSegment_083_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2592 27 27, g32p_row02_traceSegment_083_2592_0027, g32p_row02_traceSegment_083_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2646 13 14, g32p_row02_traceSegment_083_2646_0013, g32p_row02_traceSegment_083_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2673 13 14, g32p_row02_traceSegment_083_2673_0013, g32p_row02_traceSegment_083_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2646 27 27, g32p_row02_traceSegment_083_2646_0027, g32p_row02_traceSegment_083_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2592 54 54, g32p_row02_traceSegment_083_2592_0054, g32p_row02_traceSegment_083_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2700 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2700 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2700 13 14, g32p_row02_traceSegment_083_2700_0013, g32p_row02_traceSegment_083_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2727 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2740 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2727 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2727 13 14, g32p_row02_traceSegment_083_2727_0013, g32p_row02_traceSegment_083_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2700 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2700 27 27, g32p_row02_traceSegment_083_2700_0027, g32p_row02_traceSegment_083_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2754 13 14, g32p_row02_traceSegment_083_2754_0013, g32p_row02_traceSegment_083_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2781 13 14, g32p_row02_traceSegment_083_2781_0013, g32p_row02_traceSegment_083_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2754 27 27, g32p_row02_traceSegment_083_2754_0027, g32p_row02_traceSegment_083_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 2700 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2700 54 54, g32p_row02_traceSegment_083_2700_0054, g32p_row02_traceSegment_083_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 2592 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2592 108 108, g32p_row02_traceSegment_083_2592_0108, g32p_row02_traceSegment_083_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2808 13 14, g32p_row02_traceSegment_083_2808_0013, g32p_row02_traceSegment_083_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2835 13 14, g32p_row02_traceSegment_083_2835_0013, g32p_row02_traceSegment_083_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2808 27 27, g32p_row02_traceSegment_083_2808_0027, g32p_row02_traceSegment_083_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2862 13 14, g32p_row02_traceSegment_083_2862_0013, g32p_row02_traceSegment_083_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2889 13 14, g32p_row02_traceSegment_083_2889_0013, g32p_row02_traceSegment_083_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2862 27 27, g32p_row02_traceSegment_083_2862_0027, g32p_row02_traceSegment_083_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2808 54 54, g32p_row02_traceSegment_083_2808_0054, g32p_row02_traceSegment_083_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2916 13 14, g32p_row02_traceSegment_083_2916_0013, g32p_row02_traceSegment_083_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2943 13 14, g32p_row02_traceSegment_083_2943_0013, g32p_row02_traceSegment_083_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2916 27 27, g32p_row02_traceSegment_083_2916_0027, g32p_row02_traceSegment_083_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2970 13 14, g32p_row02_traceSegment_083_2970_0013, g32p_row02_traceSegment_083_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3010 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 2997 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2997 13 14, g32p_row02_traceSegment_083_2997_0013, g32p_row02_traceSegment_083_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 2970 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2970 27 27, g32p_row02_traceSegment_083_2970_0027, g32p_row02_traceSegment_083_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 2916 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2916 54 54, g32p_row02_traceSegment_083_2916_0054, g32p_row02_traceSegment_083_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 2808 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2808 108 108, g32p_row02_traceSegment_083_2808_0108, g32p_row02_traceSegment_083_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_083 2592 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2592 216 216, g32p_row02_traceSegment_083_2592_0216, g32p_row02_traceSegment_083_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3024 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3037 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3024 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3024 13 14, g32p_row02_traceSegment_083_3024_0013, g32p_row02_traceSegment_083_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3051 13 14, g32p_row02_traceSegment_083_3051_0013, g32p_row02_traceSegment_083_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 3024 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3024 27 27, g32p_row02_traceSegment_083_3024_0027, g32p_row02_traceSegment_083_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3091 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3078 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3078 13 14, g32p_row02_traceSegment_083_3078_0013, g32p_row02_traceSegment_083_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3118 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3105 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3105 13 14, g32p_row02_traceSegment_083_3105_0013, g32p_row02_traceSegment_083_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 3078 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3078 27 27, g32p_row02_traceSegment_083_3078_0027, g32p_row02_traceSegment_083_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 3024 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3024 54 54, g32p_row02_traceSegment_083_3024_0054, g32p_row02_traceSegment_083_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3132 13 14, g32p_row02_traceSegment_083_3132_0013, g32p_row02_traceSegment_083_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3159 13 14, g32p_row02_traceSegment_083_3159_0013, g32p_row02_traceSegment_083_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3132 27 27, g32p_row02_traceSegment_083_3132_0027, g32p_row02_traceSegment_083_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3186 13 14, g32p_row02_traceSegment_083_3186_0013, g32p_row02_traceSegment_083_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3213 13 14, g32p_row02_traceSegment_083_3213_0013, g32p_row02_traceSegment_083_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3186 27 27, g32p_row02_traceSegment_083_3186_0027, g32p_row02_traceSegment_083_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3132 54 54, g32p_row02_traceSegment_083_3132_0054, g32p_row02_traceSegment_083_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 3024 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3024 108 108, g32p_row02_traceSegment_083_3024_0108, g32p_row02_traceSegment_083_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3240 13 14, g32p_row02_traceSegment_083_3240_0013, g32p_row02_traceSegment_083_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3267 13 14, g32p_row02_traceSegment_083_3267_0013, g32p_row02_traceSegment_083_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3240 27 27, g32p_row02_traceSegment_083_3240_0027, g32p_row02_traceSegment_083_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3294 13 14, g32p_row02_traceSegment_083_3294_0013, g32p_row02_traceSegment_083_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3321 13 14, g32p_row02_traceSegment_083_3321_0013, g32p_row02_traceSegment_083_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3294 27 27, g32p_row02_traceSegment_083_3294_0027, g32p_row02_traceSegment_083_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3240 54 54, g32p_row02_traceSegment_083_3240_0054, g32p_row02_traceSegment_083_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3348 13 14, g32p_row02_traceSegment_083_3348_0013, g32p_row02_traceSegment_083_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3375 13 14, g32p_row02_traceSegment_083_3375_0013, g32p_row02_traceSegment_083_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3348 27 27, g32p_row02_traceSegment_083_3348_0027, g32p_row02_traceSegment_083_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3402 13 14, g32p_row02_traceSegment_083_3402_0013, g32p_row02_traceSegment_083_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_083 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_083 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_083_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_083 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3429 13 14, g32p_row02_traceSegment_083_3429_0013, g32p_row02_traceSegment_083_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_083 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3402 27 27, g32p_row02_traceSegment_083_3402_0027, g32p_row02_traceSegment_083_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_083 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3348 54 54, g32p_row02_traceSegment_083_3348_0054, g32p_row02_traceSegment_083_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_083 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3240 108 108, g32p_row02_traceSegment_083_3240_0108, g32p_row02_traceSegment_083_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_083_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_083 3024 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 3024 216 216, g32p_row02_traceSegment_083_3024_0216, g32p_row02_traceSegment_083_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_083_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_083 2592 864 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 2592 432 432, g32p_row02_traceSegment_083_2592_0432, g32p_row02_traceSegment_083_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_083_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_083 1728 1728 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 1728 864 864, g32p_row02_traceSegment_083_1728_0864, g32p_row02_traceSegment_083_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_083_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_083 0 3456 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_083 0 1728 1728, g32p_row02_traceSegment_083_0000_1728, g32p_row02_traceSegment_083_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 83 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_083_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_084 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 84 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_084_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 0 13 14, g32p_row02_traceSegment_084_0000_0013, g32p_row02_traceSegment_084_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 27 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 40 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 27 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 27 13 14, g32p_row02_traceSegment_084_0027_0013, g32p_row02_traceSegment_084_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 0 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 0 27 27, g32p_row02_traceSegment_084_0000_0027, g32p_row02_traceSegment_084_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 67 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 54 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 54 13 14, g32p_row02_traceSegment_084_0054_0013, g32p_row02_traceSegment_084_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 81 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 94 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 81 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 81 13 14, g32p_row02_traceSegment_084_0081_0013, g32p_row02_traceSegment_084_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 54 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 54 27 27, g32p_row02_traceSegment_084_0054_0027, g32p_row02_traceSegment_084_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 0 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 0 54 54, g32p_row02_traceSegment_084_0000_0054, g32p_row02_traceSegment_084_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 108 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 108 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 108 13 14, g32p_row02_traceSegment_084_0108_0013, g32p_row02_traceSegment_084_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 135 13 14, g32p_row02_traceSegment_084_0135_0013, g32p_row02_traceSegment_084_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 108 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 108 27 27, g32p_row02_traceSegment_084_0108_0027, g32p_row02_traceSegment_084_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 162 13 14, g32p_row02_traceSegment_084_0162_0013, g32p_row02_traceSegment_084_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 189 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 189 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 189 13 14, g32p_row02_traceSegment_084_0189_0013, g32p_row02_traceSegment_084_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 162 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 162 27 27, g32p_row02_traceSegment_084_0162_0027, g32p_row02_traceSegment_084_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 108 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 108 54 54, g32p_row02_traceSegment_084_0108_0054, g32p_row02_traceSegment_084_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 0 216 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 0 108 108, g32p_row02_traceSegment_084_0000_0108, g32p_row02_traceSegment_084_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 216 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 216 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 216 13 14, g32p_row02_traceSegment_084_0216_0013, g32p_row02_traceSegment_084_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 243 13 14, g32p_row02_traceSegment_084_0243_0013, g32p_row02_traceSegment_084_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 216 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 216 27 27, g32p_row02_traceSegment_084_0216_0027, g32p_row02_traceSegment_084_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 270 13 14, g32p_row02_traceSegment_084_0270_0013, g32p_row02_traceSegment_084_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 297 13 14, g32p_row02_traceSegment_084_0297_0013, g32p_row02_traceSegment_084_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 270 27 27, g32p_row02_traceSegment_084_0270_0027, g32p_row02_traceSegment_084_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 216 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 216 54 54, g32p_row02_traceSegment_084_0216_0054, g32p_row02_traceSegment_084_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 324 13 14, g32p_row02_traceSegment_084_0324_0013, g32p_row02_traceSegment_084_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 351 13 14, g32p_row02_traceSegment_084_0351_0013, g32p_row02_traceSegment_084_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 324 27 27, g32p_row02_traceSegment_084_0324_0027, g32p_row02_traceSegment_084_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 378 13 14, g32p_row02_traceSegment_084_0378_0013, g32p_row02_traceSegment_084_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 405 13 14, g32p_row02_traceSegment_084_0405_0013, g32p_row02_traceSegment_084_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 378 27 27, g32p_row02_traceSegment_084_0378_0027, g32p_row02_traceSegment_084_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 324 54 54, g32p_row02_traceSegment_084_0324_0054, g32p_row02_traceSegment_084_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 216 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 216 108 108, g32p_row02_traceSegment_084_0216_0108, g32p_row02_traceSegment_084_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_084 0 432 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 0 216 216, g32p_row02_traceSegment_084_0000_0216, g32p_row02_traceSegment_084_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 432 13 14, g32p_row02_traceSegment_084_0432_0013, g32p_row02_traceSegment_084_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 459 13 14, g32p_row02_traceSegment_084_0459_0013, g32p_row02_traceSegment_084_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 432 27 27, g32p_row02_traceSegment_084_0432_0027, g32p_row02_traceSegment_084_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 486 13 14, g32p_row02_traceSegment_084_0486_0013, g32p_row02_traceSegment_084_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 513 13 14, g32p_row02_traceSegment_084_0513_0013, g32p_row02_traceSegment_084_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 486 27 27, g32p_row02_traceSegment_084_0486_0027, g32p_row02_traceSegment_084_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 432 54 54, g32p_row02_traceSegment_084_0432_0054, g32p_row02_traceSegment_084_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 540 13 14, g32p_row02_traceSegment_084_0540_0013, g32p_row02_traceSegment_084_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 567 13 14, g32p_row02_traceSegment_084_0567_0013, g32p_row02_traceSegment_084_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 540 27 27, g32p_row02_traceSegment_084_0540_0027, g32p_row02_traceSegment_084_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 594 13 14, g32p_row02_traceSegment_084_0594_0013, g32p_row02_traceSegment_084_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 621 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 634 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 621 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 621 13 14, g32p_row02_traceSegment_084_0621_0013, g32p_row02_traceSegment_084_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 594 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 594 27 27, g32p_row02_traceSegment_084_0594_0027, g32p_row02_traceSegment_084_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 540 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 540 54 54, g32p_row02_traceSegment_084_0540_0054, g32p_row02_traceSegment_084_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 432 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 432 108 108, g32p_row02_traceSegment_084_0432_0108, g32p_row02_traceSegment_084_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 648 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 648 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 648 13 14, g32p_row02_traceSegment_084_0648_0013, g32p_row02_traceSegment_084_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 675 13 14, g32p_row02_traceSegment_084_0675_0013, g32p_row02_traceSegment_084_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 648 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 648 27 27, g32p_row02_traceSegment_084_0648_0027, g32p_row02_traceSegment_084_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 702 13 14, g32p_row02_traceSegment_084_0702_0013, g32p_row02_traceSegment_084_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 729 13 14, g32p_row02_traceSegment_084_0729_0013, g32p_row02_traceSegment_084_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 702 27 27, g32p_row02_traceSegment_084_0702_0027, g32p_row02_traceSegment_084_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 648 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 648 54 54, g32p_row02_traceSegment_084_0648_0054, g32p_row02_traceSegment_084_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 756 13 14, g32p_row02_traceSegment_084_0756_0013, g32p_row02_traceSegment_084_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 783 13 14, g32p_row02_traceSegment_084_0783_0013, g32p_row02_traceSegment_084_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 756 27 27, g32p_row02_traceSegment_084_0756_0027, g32p_row02_traceSegment_084_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 810 13 14, g32p_row02_traceSegment_084_0810_0013, g32p_row02_traceSegment_084_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 837 13 14, g32p_row02_traceSegment_084_0837_0013, g32p_row02_traceSegment_084_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 810 27 27, g32p_row02_traceSegment_084_0810_0027, g32p_row02_traceSegment_084_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 756 54 54, g32p_row02_traceSegment_084_0756_0054, g32p_row02_traceSegment_084_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 648 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 648 108 108, g32p_row02_traceSegment_084_0648_0108, g32p_row02_traceSegment_084_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_084 432 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 432 216 216, g32p_row02_traceSegment_084_0432_0216, g32p_row02_traceSegment_084_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_084 0 864 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 0 432 432, g32p_row02_traceSegment_084_0000_0432, g32p_row02_traceSegment_084_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 864 13 14, g32p_row02_traceSegment_084_0864_0013, g32p_row02_traceSegment_084_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 891 13 14, g32p_row02_traceSegment_084_0891_0013, g32p_row02_traceSegment_084_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 864 27 27, g32p_row02_traceSegment_084_0864_0027, g32p_row02_traceSegment_084_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 918 13 14, g32p_row02_traceSegment_084_0918_0013, g32p_row02_traceSegment_084_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 945 13 14, g32p_row02_traceSegment_084_0945_0013, g32p_row02_traceSegment_084_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 918 27 27, g32p_row02_traceSegment_084_0918_0027, g32p_row02_traceSegment_084_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 864 54 54, g32p_row02_traceSegment_084_0864_0054, g32p_row02_traceSegment_084_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 972 13 14, g32p_row02_traceSegment_084_0972_0013, g32p_row02_traceSegment_084_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 999 13 14, g32p_row02_traceSegment_084_0999_0013, g32p_row02_traceSegment_084_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 972 27 27, g32p_row02_traceSegment_084_0972_0027, g32p_row02_traceSegment_084_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1039 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1026 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1026 13 14, g32p_row02_traceSegment_084_1026_0013, g32p_row02_traceSegment_084_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1066 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1053 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1053 13 14, g32p_row02_traceSegment_084_1053_0013, g32p_row02_traceSegment_084_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1026 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1026 27 27, g32p_row02_traceSegment_084_1026_0027, g32p_row02_traceSegment_084_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 972 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 972 54 54, g32p_row02_traceSegment_084_0972_0054, g32p_row02_traceSegment_084_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 864 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 864 108 108, g32p_row02_traceSegment_084_0864_0108, g32p_row02_traceSegment_084_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1080 13 14, g32p_row02_traceSegment_084_1080_0013, g32p_row02_traceSegment_084_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1107 13 14, g32p_row02_traceSegment_084_1107_0013, g32p_row02_traceSegment_084_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1080 27 27, g32p_row02_traceSegment_084_1080_0027, g32p_row02_traceSegment_084_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1134 13 14, g32p_row02_traceSegment_084_1134_0013, g32p_row02_traceSegment_084_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1161 13 14, g32p_row02_traceSegment_084_1161_0013, g32p_row02_traceSegment_084_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1134 27 27, g32p_row02_traceSegment_084_1134_0027, g32p_row02_traceSegment_084_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1080 54 54, g32p_row02_traceSegment_084_1080_0054, g32p_row02_traceSegment_084_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1188 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1201 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1188 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1188 13 14, g32p_row02_traceSegment_084_1188_0013, g32p_row02_traceSegment_084_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1215 13 14, g32p_row02_traceSegment_084_1215_0013, g32p_row02_traceSegment_084_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1188 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1188 27 27, g32p_row02_traceSegment_084_1188_0027, g32p_row02_traceSegment_084_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1242 13 14, g32p_row02_traceSegment_084_1242_0013, g32p_row02_traceSegment_084_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1269 13 14, g32p_row02_traceSegment_084_1269_0013, g32p_row02_traceSegment_084_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1242 27 27, g32p_row02_traceSegment_084_1242_0027, g32p_row02_traceSegment_084_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 1188 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1188 54 54, g32p_row02_traceSegment_084_1188_0054, g32p_row02_traceSegment_084_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 1080 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1080 108 108, g32p_row02_traceSegment_084_1080_0108, g32p_row02_traceSegment_084_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_084 864 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 864 216 216, g32p_row02_traceSegment_084_0864_0216, g32p_row02_traceSegment_084_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1309 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1296 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1296 13 14, g32p_row02_traceSegment_084_1296_0013, g32p_row02_traceSegment_084_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1336 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1323 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1323 13 14, g32p_row02_traceSegment_084_1323_0013, g32p_row02_traceSegment_084_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1296 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1296 27 27, g32p_row02_traceSegment_084_1296_0027, g32p_row02_traceSegment_084_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1350 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1363 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1350 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1350 13 14, g32p_row02_traceSegment_084_1350_0013, g32p_row02_traceSegment_084_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1377 13 14, g32p_row02_traceSegment_084_1377_0013, g32p_row02_traceSegment_084_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1350 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1350 27 27, g32p_row02_traceSegment_084_1350_0027, g32p_row02_traceSegment_084_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 1296 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1296 54 54, g32p_row02_traceSegment_084_1296_0054, g32p_row02_traceSegment_084_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1404 13 14, g32p_row02_traceSegment_084_1404_0013, g32p_row02_traceSegment_084_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1431 13 14, g32p_row02_traceSegment_084_1431_0013, g32p_row02_traceSegment_084_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1404 27 27, g32p_row02_traceSegment_084_1404_0027, g32p_row02_traceSegment_084_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1471 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1458 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1458 13 14, g32p_row02_traceSegment_084_1458_0013, g32p_row02_traceSegment_084_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1485 13 14, g32p_row02_traceSegment_084_1485_0013, g32p_row02_traceSegment_084_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1458 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1458 27 27, g32p_row02_traceSegment_084_1458_0027, g32p_row02_traceSegment_084_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 1404 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1404 54 54, g32p_row02_traceSegment_084_1404_0054, g32p_row02_traceSegment_084_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 1296 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1296 108 108, g32p_row02_traceSegment_084_1296_0108, g32p_row02_traceSegment_084_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1512 13 14, g32p_row02_traceSegment_084_1512_0013, g32p_row02_traceSegment_084_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1539 13 14, g32p_row02_traceSegment_084_1539_0013, g32p_row02_traceSegment_084_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1512 27 27, g32p_row02_traceSegment_084_1512_0027, g32p_row02_traceSegment_084_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1566 13 14, g32p_row02_traceSegment_084_1566_0013, g32p_row02_traceSegment_084_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1606 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1593 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1593 13 14, g32p_row02_traceSegment_084_1593_0013, g32p_row02_traceSegment_084_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1566 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1566 27 27, g32p_row02_traceSegment_084_1566_0027, g32p_row02_traceSegment_084_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 1512 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1512 54 54, g32p_row02_traceSegment_084_1512_0054, g32p_row02_traceSegment_084_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1620 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1620 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1620 13 14, g32p_row02_traceSegment_084_1620_0013, g32p_row02_traceSegment_084_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1647 13 14, g32p_row02_traceSegment_084_1647_0013, g32p_row02_traceSegment_084_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1620 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1620 27 27, g32p_row02_traceSegment_084_1620_0027, g32p_row02_traceSegment_084_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1687 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1674 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1674 13 14, g32p_row02_traceSegment_084_1674_0013, g32p_row02_traceSegment_084_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1701 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1701 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1701 13 14, g32p_row02_traceSegment_084_1701_0013, g32p_row02_traceSegment_084_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1674 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1674 27 27, g32p_row02_traceSegment_084_1674_0027, g32p_row02_traceSegment_084_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 1620 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1620 54 54, g32p_row02_traceSegment_084_1620_0054, g32p_row02_traceSegment_084_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 1512 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1512 108 108, g32p_row02_traceSegment_084_1512_0108, g32p_row02_traceSegment_084_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_084 1296 432 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1296 216 216, g32p_row02_traceSegment_084_1296_0216, g32p_row02_traceSegment_084_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_084 864 864 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 864 432 432, g32p_row02_traceSegment_084_0864_0432, g32p_row02_traceSegment_084_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_084 0 1728 = [0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 0 864 864, g32p_row02_traceSegment_084_0000_0864, g32p_row02_traceSegment_084_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1741 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1728 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1728 13 14, g32p_row02_traceSegment_084_1728_0013, g32p_row02_traceSegment_084_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1755 13 14, g32p_row02_traceSegment_084_1755_0013, g32p_row02_traceSegment_084_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1728 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1728 27 27, g32p_row02_traceSegment_084_1728_0027, g32p_row02_traceSegment_084_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1782 13 14, g32p_row02_traceSegment_084_1782_0013, g32p_row02_traceSegment_084_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1809 13 14, g32p_row02_traceSegment_084_1809_0013, g32p_row02_traceSegment_084_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1782 27 27, g32p_row02_traceSegment_084_1782_0027, g32p_row02_traceSegment_084_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 1728 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1728 54 54, g32p_row02_traceSegment_084_1728_0054, g32p_row02_traceSegment_084_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1836 13 14, g32p_row02_traceSegment_084_1836_0013, g32p_row02_traceSegment_084_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1863 13 14, g32p_row02_traceSegment_084_1863_0013, g32p_row02_traceSegment_084_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1836 27 27, g32p_row02_traceSegment_084_1836_0027, g32p_row02_traceSegment_084_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1890 13 14, g32p_row02_traceSegment_084_1890_0013, g32p_row02_traceSegment_084_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1917 13 14, g32p_row02_traceSegment_084_1917_0013, g32p_row02_traceSegment_084_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1890 27 27, g32p_row02_traceSegment_084_1890_0027, g32p_row02_traceSegment_084_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1836 54 54, g32p_row02_traceSegment_084_1836_0054, g32p_row02_traceSegment_084_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 1728 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1728 108 108, g32p_row02_traceSegment_084_1728_0108, g32p_row02_traceSegment_084_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1944 13 14, g32p_row02_traceSegment_084_1944_0013, g32p_row02_traceSegment_084_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1971 13 14, g32p_row02_traceSegment_084_1971_0013, g32p_row02_traceSegment_084_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1944 27 27, g32p_row02_traceSegment_084_1944_0027, g32p_row02_traceSegment_084_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 1998 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 1998 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1998 13 14, g32p_row02_traceSegment_084_1998_0013, g32p_row02_traceSegment_084_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2025 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2025 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2025 13 14, g32p_row02_traceSegment_084_2025_0013, g32p_row02_traceSegment_084_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 1998 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1998 27 27, g32p_row02_traceSegment_084_1998_0027, g32p_row02_traceSegment_084_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 1944 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1944 54 54, g32p_row02_traceSegment_084_1944_0054, g32p_row02_traceSegment_084_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2052 13 14, g32p_row02_traceSegment_084_2052_0013, g32p_row02_traceSegment_084_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2079 13 14, g32p_row02_traceSegment_084_2079_0013, g32p_row02_traceSegment_084_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2052 27 27, g32p_row02_traceSegment_084_2052_0027, g32p_row02_traceSegment_084_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2106 13 14, g32p_row02_traceSegment_084_2106_0013, g32p_row02_traceSegment_084_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2133 13 14, g32p_row02_traceSegment_084_2133_0013, g32p_row02_traceSegment_084_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2106 27 27, g32p_row02_traceSegment_084_2106_0027, g32p_row02_traceSegment_084_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2052 54 54, g32p_row02_traceSegment_084_2052_0054, g32p_row02_traceSegment_084_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 1944 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1944 108 108, g32p_row02_traceSegment_084_1944_0108, g32p_row02_traceSegment_084_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_084 1728 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1728 216 216, g32p_row02_traceSegment_084_1728_0216, g32p_row02_traceSegment_084_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2160 13 14, g32p_row02_traceSegment_084_2160_0013, g32p_row02_traceSegment_084_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2187 13 14, g32p_row02_traceSegment_084_2187_0013, g32p_row02_traceSegment_084_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2160 27 27, g32p_row02_traceSegment_084_2160_0027, g32p_row02_traceSegment_084_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2214 13 14, g32p_row02_traceSegment_084_2214_0013, g32p_row02_traceSegment_084_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2241 13 14, g32p_row02_traceSegment_084_2241_0013, g32p_row02_traceSegment_084_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2214 27 27, g32p_row02_traceSegment_084_2214_0027, g32p_row02_traceSegment_084_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2160 54 54, g32p_row02_traceSegment_084_2160_0054, g32p_row02_traceSegment_084_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2268 13 14, g32p_row02_traceSegment_084_2268_0013, g32p_row02_traceSegment_084_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2295 13 14, g32p_row02_traceSegment_084_2295_0013, g32p_row02_traceSegment_084_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2268 27 27, g32p_row02_traceSegment_084_2268_0027, g32p_row02_traceSegment_084_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2322 13 14, g32p_row02_traceSegment_084_2322_0013, g32p_row02_traceSegment_084_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2349 13 14, g32p_row02_traceSegment_084_2349_0013, g32p_row02_traceSegment_084_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2322 27 27, g32p_row02_traceSegment_084_2322_0027, g32p_row02_traceSegment_084_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2268 54 54, g32p_row02_traceSegment_084_2268_0054, g32p_row02_traceSegment_084_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2160 108 108, g32p_row02_traceSegment_084_2160_0108, g32p_row02_traceSegment_084_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2376 13 14, g32p_row02_traceSegment_084_2376_0013, g32p_row02_traceSegment_084_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2403 13 14, g32p_row02_traceSegment_084_2403_0013, g32p_row02_traceSegment_084_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2376 27 27, g32p_row02_traceSegment_084_2376_0027, g32p_row02_traceSegment_084_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2430 13 14, g32p_row02_traceSegment_084_2430_0013, g32p_row02_traceSegment_084_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2457 13 14, g32p_row02_traceSegment_084_2457_0013, g32p_row02_traceSegment_084_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2430 27 27, g32p_row02_traceSegment_084_2430_0027, g32p_row02_traceSegment_084_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2376 54 54, g32p_row02_traceSegment_084_2376_0054, g32p_row02_traceSegment_084_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2484 13 14, g32p_row02_traceSegment_084_2484_0013, g32p_row02_traceSegment_084_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2511 13 14, g32p_row02_traceSegment_084_2511_0013, g32p_row02_traceSegment_084_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2484 27 27, g32p_row02_traceSegment_084_2484_0027, g32p_row02_traceSegment_084_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2538 13 14, g32p_row02_traceSegment_084_2538_0013, g32p_row02_traceSegment_084_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2565 13 14, g32p_row02_traceSegment_084_2565_0013, g32p_row02_traceSegment_084_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2538 27 27, g32p_row02_traceSegment_084_2538_0027, g32p_row02_traceSegment_084_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2484 54 54, g32p_row02_traceSegment_084_2484_0054, g32p_row02_traceSegment_084_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2376 108 108, g32p_row02_traceSegment_084_2376_0108, g32p_row02_traceSegment_084_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_084 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2160 216 216, g32p_row02_traceSegment_084_2160_0216, g32p_row02_traceSegment_084_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_084 1728 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1728 432 432, g32p_row02_traceSegment_084_1728_0432, g32p_row02_traceSegment_084_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2592 13 14, g32p_row02_traceSegment_084_2592_0013, g32p_row02_traceSegment_084_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2619 13 14, g32p_row02_traceSegment_084_2619_0013, g32p_row02_traceSegment_084_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2592 27 27, g32p_row02_traceSegment_084_2592_0027, g32p_row02_traceSegment_084_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2646 13 14, g32p_row02_traceSegment_084_2646_0013, g32p_row02_traceSegment_084_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2673 13 14, g32p_row02_traceSegment_084_2673_0013, g32p_row02_traceSegment_084_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2646 27 27, g32p_row02_traceSegment_084_2646_0027, g32p_row02_traceSegment_084_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2592 54 54, g32p_row02_traceSegment_084_2592_0054, g32p_row02_traceSegment_084_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2700 13 14, g32p_row02_traceSegment_084_2700_0013, g32p_row02_traceSegment_084_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2727 13 14, g32p_row02_traceSegment_084_2727_0013, g32p_row02_traceSegment_084_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2700 27 27, g32p_row02_traceSegment_084_2700_0027, g32p_row02_traceSegment_084_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2754 13 14, g32p_row02_traceSegment_084_2754_0013, g32p_row02_traceSegment_084_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2781 13 14, g32p_row02_traceSegment_084_2781_0013, g32p_row02_traceSegment_084_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2754 27 27, g32p_row02_traceSegment_084_2754_0027, g32p_row02_traceSegment_084_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2700 54 54, g32p_row02_traceSegment_084_2700_0054, g32p_row02_traceSegment_084_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2592 108 108, g32p_row02_traceSegment_084_2592_0108, g32p_row02_traceSegment_084_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2808 13 14, g32p_row02_traceSegment_084_2808_0013, g32p_row02_traceSegment_084_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2835 13 14, g32p_row02_traceSegment_084_2835_0013, g32p_row02_traceSegment_084_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2808 27 27, g32p_row02_traceSegment_084_2808_0027, g32p_row02_traceSegment_084_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2862 13 14, g32p_row02_traceSegment_084_2862_0013, g32p_row02_traceSegment_084_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2889 13 14, g32p_row02_traceSegment_084_2889_0013, g32p_row02_traceSegment_084_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2862 27 27, g32p_row02_traceSegment_084_2862_0027, g32p_row02_traceSegment_084_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2808 54 54, g32p_row02_traceSegment_084_2808_0054, g32p_row02_traceSegment_084_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2916 13 14, g32p_row02_traceSegment_084_2916_0013, g32p_row02_traceSegment_084_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2943 13 14, g32p_row02_traceSegment_084_2943_0013, g32p_row02_traceSegment_084_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2916 27 27, g32p_row02_traceSegment_084_2916_0027, g32p_row02_traceSegment_084_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2970 13 14, g32p_row02_traceSegment_084_2970_0013, g32p_row02_traceSegment_084_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2997 13 14, g32p_row02_traceSegment_084_2997_0013, g32p_row02_traceSegment_084_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2970 27 27, g32p_row02_traceSegment_084_2970_0027, g32p_row02_traceSegment_084_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2916 54 54, g32p_row02_traceSegment_084_2916_0054, g32p_row02_traceSegment_084_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2808 108 108, g32p_row02_traceSegment_084_2808_0108, g32p_row02_traceSegment_084_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_084 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2592 216 216, g32p_row02_traceSegment_084_2592_0216, g32p_row02_traceSegment_084_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3024 13 14, g32p_row02_traceSegment_084_3024_0013, g32p_row02_traceSegment_084_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3051 13 14, g32p_row02_traceSegment_084_3051_0013, g32p_row02_traceSegment_084_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3024 27 27, g32p_row02_traceSegment_084_3024_0027, g32p_row02_traceSegment_084_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3078 13 14, g32p_row02_traceSegment_084_3078_0013, g32p_row02_traceSegment_084_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3105 13 14, g32p_row02_traceSegment_084_3105_0013, g32p_row02_traceSegment_084_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3078 27 27, g32p_row02_traceSegment_084_3078_0027, g32p_row02_traceSegment_084_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3024 54 54, g32p_row02_traceSegment_084_3024_0054, g32p_row02_traceSegment_084_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3132 13 14, g32p_row02_traceSegment_084_3132_0013, g32p_row02_traceSegment_084_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3159 13 14, g32p_row02_traceSegment_084_3159_0013, g32p_row02_traceSegment_084_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3132 27 27, g32p_row02_traceSegment_084_3132_0027, g32p_row02_traceSegment_084_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3186 13 14, g32p_row02_traceSegment_084_3186_0013, g32p_row02_traceSegment_084_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3213 13 14, g32p_row02_traceSegment_084_3213_0013, g32p_row02_traceSegment_084_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3186 27 27, g32p_row02_traceSegment_084_3186_0027, g32p_row02_traceSegment_084_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3132 54 54, g32p_row02_traceSegment_084_3132_0054, g32p_row02_traceSegment_084_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3024 108 108, g32p_row02_traceSegment_084_3024_0108, g32p_row02_traceSegment_084_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3240 13 14, g32p_row02_traceSegment_084_3240_0013, g32p_row02_traceSegment_084_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3267 13 14, g32p_row02_traceSegment_084_3267_0013, g32p_row02_traceSegment_084_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3240 27 27, g32p_row02_traceSegment_084_3240_0027, g32p_row02_traceSegment_084_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3294 13 14, g32p_row02_traceSegment_084_3294_0013, g32p_row02_traceSegment_084_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3321 13 14, g32p_row02_traceSegment_084_3321_0013, g32p_row02_traceSegment_084_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3294 27 27, g32p_row02_traceSegment_084_3294_0027, g32p_row02_traceSegment_084_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3240 54 54, g32p_row02_traceSegment_084_3240_0054, g32p_row02_traceSegment_084_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3348 13 14, g32p_row02_traceSegment_084_3348_0013, g32p_row02_traceSegment_084_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3375 13 14, g32p_row02_traceSegment_084_3375_0013, g32p_row02_traceSegment_084_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3348 27 27, g32p_row02_traceSegment_084_3348_0027, g32p_row02_traceSegment_084_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3402 13 14, g32p_row02_traceSegment_084_3402_0013, g32p_row02_traceSegment_084_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_084 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_084 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_084_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_084 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3429 13 14, g32p_row02_traceSegment_084_3429_0013, g32p_row02_traceSegment_084_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_084 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3402 27 27, g32p_row02_traceSegment_084_3402_0027, g32p_row02_traceSegment_084_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_084 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3348 54 54, g32p_row02_traceSegment_084_3348_0054, g32p_row02_traceSegment_084_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_084 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3240 108 108, g32p_row02_traceSegment_084_3240_0108, g32p_row02_traceSegment_084_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_084_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_084 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 3024 216 216, g32p_row02_traceSegment_084_3024_0216, g32p_row02_traceSegment_084_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_084_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_084 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 2592 432 432, g32p_row02_traceSegment_084_2592_0432, g32p_row02_traceSegment_084_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_084_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_084 1728 1728 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 1728 864 864, g32p_row02_traceSegment_084_1728_0864, g32p_row02_traceSegment_084_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_084_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_084 0 3456 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_084 0 1728 1728, g32p_row02_traceSegment_084_0000_1728, g32p_row02_traceSegment_084_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 84 = [0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_084_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_085 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 85 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_085_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 0 13 14, g32p_row02_traceSegment_085_0000_0013, g32p_row02_traceSegment_085_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 27 13 14, g32p_row02_traceSegment_085_0027_0013, g32p_row02_traceSegment_085_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 0 27 27, g32p_row02_traceSegment_085_0000_0027, g32p_row02_traceSegment_085_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 54 13 14, g32p_row02_traceSegment_085_0054_0013, g32p_row02_traceSegment_085_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 81 13 14, g32p_row02_traceSegment_085_0081_0013, g32p_row02_traceSegment_085_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 54 27 27, g32p_row02_traceSegment_085_0054_0027, g32p_row02_traceSegment_085_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 0 54 54, g32p_row02_traceSegment_085_0000_0054, g32p_row02_traceSegment_085_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 108 13 14, g32p_row02_traceSegment_085_0108_0013, g32p_row02_traceSegment_085_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 135 13 14, g32p_row02_traceSegment_085_0135_0013, g32p_row02_traceSegment_085_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 108 27 27, g32p_row02_traceSegment_085_0108_0027, g32p_row02_traceSegment_085_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 162 13 14, g32p_row02_traceSegment_085_0162_0013, g32p_row02_traceSegment_085_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 189 13 14, g32p_row02_traceSegment_085_0189_0013, g32p_row02_traceSegment_085_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 162 27 27, g32p_row02_traceSegment_085_0162_0027, g32p_row02_traceSegment_085_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 108 54 54, g32p_row02_traceSegment_085_0108_0054, g32p_row02_traceSegment_085_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 0 108 108, g32p_row02_traceSegment_085_0000_0108, g32p_row02_traceSegment_085_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 216 13 14, g32p_row02_traceSegment_085_0216_0013, g32p_row02_traceSegment_085_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 243 13 14, g32p_row02_traceSegment_085_0243_0013, g32p_row02_traceSegment_085_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 216 27 27, g32p_row02_traceSegment_085_0216_0027, g32p_row02_traceSegment_085_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 270 13 14, g32p_row02_traceSegment_085_0270_0013, g32p_row02_traceSegment_085_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 297 13 14, g32p_row02_traceSegment_085_0297_0013, g32p_row02_traceSegment_085_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 270 27 27, g32p_row02_traceSegment_085_0270_0027, g32p_row02_traceSegment_085_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 216 54 54, g32p_row02_traceSegment_085_0216_0054, g32p_row02_traceSegment_085_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 324 13 14, g32p_row02_traceSegment_085_0324_0013, g32p_row02_traceSegment_085_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 351 13 14, g32p_row02_traceSegment_085_0351_0013, g32p_row02_traceSegment_085_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 324 27 27, g32p_row02_traceSegment_085_0324_0027, g32p_row02_traceSegment_085_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 378 13 14, g32p_row02_traceSegment_085_0378_0013, g32p_row02_traceSegment_085_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 405 13 14, g32p_row02_traceSegment_085_0405_0013, g32p_row02_traceSegment_085_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 378 27 27, g32p_row02_traceSegment_085_0378_0027, g32p_row02_traceSegment_085_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 324 54 54, g32p_row02_traceSegment_085_0324_0054, g32p_row02_traceSegment_085_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 216 108 108, g32p_row02_traceSegment_085_0216_0108, g32p_row02_traceSegment_085_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_085 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 0 216 216, g32p_row02_traceSegment_085_0000_0216, g32p_row02_traceSegment_085_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 432 13 14, g32p_row02_traceSegment_085_0432_0013, g32p_row02_traceSegment_085_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 459 13 14, g32p_row02_traceSegment_085_0459_0013, g32p_row02_traceSegment_085_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 432 27 27, g32p_row02_traceSegment_085_0432_0027, g32p_row02_traceSegment_085_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 486 13 14, g32p_row02_traceSegment_085_0486_0013, g32p_row02_traceSegment_085_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 513 13 14, g32p_row02_traceSegment_085_0513_0013, g32p_row02_traceSegment_085_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 486 27 27, g32p_row02_traceSegment_085_0486_0027, g32p_row02_traceSegment_085_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 432 54 54, g32p_row02_traceSegment_085_0432_0054, g32p_row02_traceSegment_085_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 540 13 14, g32p_row02_traceSegment_085_0540_0013, g32p_row02_traceSegment_085_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 567 13 14, g32p_row02_traceSegment_085_0567_0013, g32p_row02_traceSegment_085_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 540 27 27, g32p_row02_traceSegment_085_0540_0027, g32p_row02_traceSegment_085_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 594 13 14, g32p_row02_traceSegment_085_0594_0013, g32p_row02_traceSegment_085_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 621 13 14, g32p_row02_traceSegment_085_0621_0013, g32p_row02_traceSegment_085_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 594 27 27, g32p_row02_traceSegment_085_0594_0027, g32p_row02_traceSegment_085_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 540 54 54, g32p_row02_traceSegment_085_0540_0054, g32p_row02_traceSegment_085_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 432 108 108, g32p_row02_traceSegment_085_0432_0108, g32p_row02_traceSegment_085_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 648 13 14, g32p_row02_traceSegment_085_0648_0013, g32p_row02_traceSegment_085_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 675 13 14, g32p_row02_traceSegment_085_0675_0013, g32p_row02_traceSegment_085_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 648 27 27, g32p_row02_traceSegment_085_0648_0027, g32p_row02_traceSegment_085_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 702 13 14, g32p_row02_traceSegment_085_0702_0013, g32p_row02_traceSegment_085_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 729 13 14, g32p_row02_traceSegment_085_0729_0013, g32p_row02_traceSegment_085_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 702 27 27, g32p_row02_traceSegment_085_0702_0027, g32p_row02_traceSegment_085_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 648 54 54, g32p_row02_traceSegment_085_0648_0054, g32p_row02_traceSegment_085_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 756 13 14, g32p_row02_traceSegment_085_0756_0013, g32p_row02_traceSegment_085_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 783 13 14, g32p_row02_traceSegment_085_0783_0013, g32p_row02_traceSegment_085_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 756 27 27, g32p_row02_traceSegment_085_0756_0027, g32p_row02_traceSegment_085_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 810 13 14, g32p_row02_traceSegment_085_0810_0013, g32p_row02_traceSegment_085_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 837 13 14, g32p_row02_traceSegment_085_0837_0013, g32p_row02_traceSegment_085_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 810 27 27, g32p_row02_traceSegment_085_0810_0027, g32p_row02_traceSegment_085_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 756 54 54, g32p_row02_traceSegment_085_0756_0054, g32p_row02_traceSegment_085_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 648 108 108, g32p_row02_traceSegment_085_0648_0108, g32p_row02_traceSegment_085_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_085 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 432 216 216, g32p_row02_traceSegment_085_0432_0216, g32p_row02_traceSegment_085_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_085 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 0 432 432, g32p_row02_traceSegment_085_0000_0432, g32p_row02_traceSegment_085_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 864 13 14, g32p_row02_traceSegment_085_0864_0013, g32p_row02_traceSegment_085_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 891 13 14, g32p_row02_traceSegment_085_0891_0013, g32p_row02_traceSegment_085_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 864 27 27, g32p_row02_traceSegment_085_0864_0027, g32p_row02_traceSegment_085_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 918 13 14, g32p_row02_traceSegment_085_0918_0013, g32p_row02_traceSegment_085_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 945 13 14, g32p_row02_traceSegment_085_0945_0013, g32p_row02_traceSegment_085_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 918 27 27, g32p_row02_traceSegment_085_0918_0027, g32p_row02_traceSegment_085_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 864 54 54, g32p_row02_traceSegment_085_0864_0054, g32p_row02_traceSegment_085_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 972 13 14, g32p_row02_traceSegment_085_0972_0013, g32p_row02_traceSegment_085_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 999 13 14, g32p_row02_traceSegment_085_0999_0013, g32p_row02_traceSegment_085_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 972 27 27, g32p_row02_traceSegment_085_0972_0027, g32p_row02_traceSegment_085_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1026 13 14, g32p_row02_traceSegment_085_1026_0013, g32p_row02_traceSegment_085_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1053 13 14, g32p_row02_traceSegment_085_1053_0013, g32p_row02_traceSegment_085_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1026 27 27, g32p_row02_traceSegment_085_1026_0027, g32p_row02_traceSegment_085_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 972 54 54, g32p_row02_traceSegment_085_0972_0054, g32p_row02_traceSegment_085_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 864 108 108, g32p_row02_traceSegment_085_0864_0108, g32p_row02_traceSegment_085_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1080 13 14, g32p_row02_traceSegment_085_1080_0013, g32p_row02_traceSegment_085_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1107 13 14, g32p_row02_traceSegment_085_1107_0013, g32p_row02_traceSegment_085_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1080 27 27, g32p_row02_traceSegment_085_1080_0027, g32p_row02_traceSegment_085_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1134 13 14, g32p_row02_traceSegment_085_1134_0013, g32p_row02_traceSegment_085_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1161 13 14, g32p_row02_traceSegment_085_1161_0013, g32p_row02_traceSegment_085_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1134 27 27, g32p_row02_traceSegment_085_1134_0027, g32p_row02_traceSegment_085_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1080 54 54, g32p_row02_traceSegment_085_1080_0054, g32p_row02_traceSegment_085_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1188 13 14, g32p_row02_traceSegment_085_1188_0013, g32p_row02_traceSegment_085_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1215 13 14, g32p_row02_traceSegment_085_1215_0013, g32p_row02_traceSegment_085_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1188 27 27, g32p_row02_traceSegment_085_1188_0027, g32p_row02_traceSegment_085_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1242 13 14, g32p_row02_traceSegment_085_1242_0013, g32p_row02_traceSegment_085_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1269 13 14, g32p_row02_traceSegment_085_1269_0013, g32p_row02_traceSegment_085_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1242 27 27, g32p_row02_traceSegment_085_1242_0027, g32p_row02_traceSegment_085_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1188 54 54, g32p_row02_traceSegment_085_1188_0054, g32p_row02_traceSegment_085_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1080 108 108, g32p_row02_traceSegment_085_1080_0108, g32p_row02_traceSegment_085_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_085 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 864 216 216, g32p_row02_traceSegment_085_0864_0216, g32p_row02_traceSegment_085_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1296 13 14, g32p_row02_traceSegment_085_1296_0013, g32p_row02_traceSegment_085_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1323 13 14, g32p_row02_traceSegment_085_1323_0013, g32p_row02_traceSegment_085_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1296 27 27, g32p_row02_traceSegment_085_1296_0027, g32p_row02_traceSegment_085_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1350 13 14, g32p_row02_traceSegment_085_1350_0013, g32p_row02_traceSegment_085_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1377 13 14, g32p_row02_traceSegment_085_1377_0013, g32p_row02_traceSegment_085_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1350 27 27, g32p_row02_traceSegment_085_1350_0027, g32p_row02_traceSegment_085_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1296 54 54, g32p_row02_traceSegment_085_1296_0054, g32p_row02_traceSegment_085_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1404 13 14, g32p_row02_traceSegment_085_1404_0013, g32p_row02_traceSegment_085_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1431 13 14, g32p_row02_traceSegment_085_1431_0013, g32p_row02_traceSegment_085_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1404 27 27, g32p_row02_traceSegment_085_1404_0027, g32p_row02_traceSegment_085_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1458 13 14, g32p_row02_traceSegment_085_1458_0013, g32p_row02_traceSegment_085_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1485 13 14, g32p_row02_traceSegment_085_1485_0013, g32p_row02_traceSegment_085_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1458 27 27, g32p_row02_traceSegment_085_1458_0027, g32p_row02_traceSegment_085_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1404 54 54, g32p_row02_traceSegment_085_1404_0054, g32p_row02_traceSegment_085_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1296 108 108, g32p_row02_traceSegment_085_1296_0108, g32p_row02_traceSegment_085_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1512 13 14, g32p_row02_traceSegment_085_1512_0013, g32p_row02_traceSegment_085_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1539 13 14, g32p_row02_traceSegment_085_1539_0013, g32p_row02_traceSegment_085_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1512 27 27, g32p_row02_traceSegment_085_1512_0027, g32p_row02_traceSegment_085_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1566 13 14, g32p_row02_traceSegment_085_1566_0013, g32p_row02_traceSegment_085_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1593 13 14, g32p_row02_traceSegment_085_1593_0013, g32p_row02_traceSegment_085_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1566 27 27, g32p_row02_traceSegment_085_1566_0027, g32p_row02_traceSegment_085_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1512 54 54, g32p_row02_traceSegment_085_1512_0054, g32p_row02_traceSegment_085_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1620 13 14, g32p_row02_traceSegment_085_1620_0013, g32p_row02_traceSegment_085_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1647 13 14, g32p_row02_traceSegment_085_1647_0013, g32p_row02_traceSegment_085_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1620 27 27, g32p_row02_traceSegment_085_1620_0027, g32p_row02_traceSegment_085_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1674 13 14, g32p_row02_traceSegment_085_1674_0013, g32p_row02_traceSegment_085_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1701 13 14, g32p_row02_traceSegment_085_1701_0013, g32p_row02_traceSegment_085_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1674 27 27, g32p_row02_traceSegment_085_1674_0027, g32p_row02_traceSegment_085_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1620 54 54, g32p_row02_traceSegment_085_1620_0054, g32p_row02_traceSegment_085_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1512 108 108, g32p_row02_traceSegment_085_1512_0108, g32p_row02_traceSegment_085_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_085 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1296 216 216, g32p_row02_traceSegment_085_1296_0216, g32p_row02_traceSegment_085_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_085 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 864 432 432, g32p_row02_traceSegment_085_0864_0432, g32p_row02_traceSegment_085_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_085 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 0 864 864, g32p_row02_traceSegment_085_0000_0864, g32p_row02_traceSegment_085_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1728 13 14, g32p_row02_traceSegment_085_1728_0013, g32p_row02_traceSegment_085_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1755 13 14, g32p_row02_traceSegment_085_1755_0013, g32p_row02_traceSegment_085_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1728 27 27, g32p_row02_traceSegment_085_1728_0027, g32p_row02_traceSegment_085_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1782 13 14, g32p_row02_traceSegment_085_1782_0013, g32p_row02_traceSegment_085_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1809 13 14, g32p_row02_traceSegment_085_1809_0013, g32p_row02_traceSegment_085_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1782 27 27, g32p_row02_traceSegment_085_1782_0027, g32p_row02_traceSegment_085_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1728 54 54, g32p_row02_traceSegment_085_1728_0054, g32p_row02_traceSegment_085_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1836 13 14, g32p_row02_traceSegment_085_1836_0013, g32p_row02_traceSegment_085_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1863 13 14, g32p_row02_traceSegment_085_1863_0013, g32p_row02_traceSegment_085_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1836 27 27, g32p_row02_traceSegment_085_1836_0027, g32p_row02_traceSegment_085_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1890 13 14, g32p_row02_traceSegment_085_1890_0013, g32p_row02_traceSegment_085_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1917 13 14, g32p_row02_traceSegment_085_1917_0013, g32p_row02_traceSegment_085_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1890 27 27, g32p_row02_traceSegment_085_1890_0027, g32p_row02_traceSegment_085_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1836 54 54, g32p_row02_traceSegment_085_1836_0054, g32p_row02_traceSegment_085_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1728 108 108, g32p_row02_traceSegment_085_1728_0108, g32p_row02_traceSegment_085_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1944 13 14, g32p_row02_traceSegment_085_1944_0013, g32p_row02_traceSegment_085_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1971 13 14, g32p_row02_traceSegment_085_1971_0013, g32p_row02_traceSegment_085_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1944 27 27, g32p_row02_traceSegment_085_1944_0027, g32p_row02_traceSegment_085_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1998 13 14, g32p_row02_traceSegment_085_1998_0013, g32p_row02_traceSegment_085_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2025 13 14, g32p_row02_traceSegment_085_2025_0013, g32p_row02_traceSegment_085_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1998 27 27, g32p_row02_traceSegment_085_1998_0027, g32p_row02_traceSegment_085_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1944 54 54, g32p_row02_traceSegment_085_1944_0054, g32p_row02_traceSegment_085_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2052 13 14, g32p_row02_traceSegment_085_2052_0013, g32p_row02_traceSegment_085_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2079 13 14, g32p_row02_traceSegment_085_2079_0013, g32p_row02_traceSegment_085_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2052 27 27, g32p_row02_traceSegment_085_2052_0027, g32p_row02_traceSegment_085_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2106 13 14, g32p_row02_traceSegment_085_2106_0013, g32p_row02_traceSegment_085_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2133 13 14, g32p_row02_traceSegment_085_2133_0013, g32p_row02_traceSegment_085_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2106 27 27, g32p_row02_traceSegment_085_2106_0027, g32p_row02_traceSegment_085_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2052 54 54, g32p_row02_traceSegment_085_2052_0054, g32p_row02_traceSegment_085_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1944 108 108, g32p_row02_traceSegment_085_1944_0108, g32p_row02_traceSegment_085_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_085 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1728 216 216, g32p_row02_traceSegment_085_1728_0216, g32p_row02_traceSegment_085_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2160 13 14, g32p_row02_traceSegment_085_2160_0013, g32p_row02_traceSegment_085_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2187 13 14, g32p_row02_traceSegment_085_2187_0013, g32p_row02_traceSegment_085_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2160 27 27, g32p_row02_traceSegment_085_2160_0027, g32p_row02_traceSegment_085_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2214 13 14, g32p_row02_traceSegment_085_2214_0013, g32p_row02_traceSegment_085_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2241 13 14, g32p_row02_traceSegment_085_2241_0013, g32p_row02_traceSegment_085_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2214 27 27, g32p_row02_traceSegment_085_2214_0027, g32p_row02_traceSegment_085_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2160 54 54, g32p_row02_traceSegment_085_2160_0054, g32p_row02_traceSegment_085_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2268 13 14, g32p_row02_traceSegment_085_2268_0013, g32p_row02_traceSegment_085_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2295 13 14, g32p_row02_traceSegment_085_2295_0013, g32p_row02_traceSegment_085_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2268 27 27, g32p_row02_traceSegment_085_2268_0027, g32p_row02_traceSegment_085_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2322 13 14, g32p_row02_traceSegment_085_2322_0013, g32p_row02_traceSegment_085_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2349 13 14, g32p_row02_traceSegment_085_2349_0013, g32p_row02_traceSegment_085_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2322 27 27, g32p_row02_traceSegment_085_2322_0027, g32p_row02_traceSegment_085_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2268 54 54, g32p_row02_traceSegment_085_2268_0054, g32p_row02_traceSegment_085_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2160 108 108, g32p_row02_traceSegment_085_2160_0108, g32p_row02_traceSegment_085_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2376 13 14, g32p_row02_traceSegment_085_2376_0013, g32p_row02_traceSegment_085_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2403 13 14, g32p_row02_traceSegment_085_2403_0013, g32p_row02_traceSegment_085_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2376 27 27, g32p_row02_traceSegment_085_2376_0027, g32p_row02_traceSegment_085_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2430 13 14, g32p_row02_traceSegment_085_2430_0013, g32p_row02_traceSegment_085_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2457 13 14, g32p_row02_traceSegment_085_2457_0013, g32p_row02_traceSegment_085_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2430 27 27, g32p_row02_traceSegment_085_2430_0027, g32p_row02_traceSegment_085_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2376 54 54, g32p_row02_traceSegment_085_2376_0054, g32p_row02_traceSegment_085_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2484 13 14, g32p_row02_traceSegment_085_2484_0013, g32p_row02_traceSegment_085_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2511 13 14, g32p_row02_traceSegment_085_2511_0013, g32p_row02_traceSegment_085_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2484 27 27, g32p_row02_traceSegment_085_2484_0027, g32p_row02_traceSegment_085_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2538 13 14, g32p_row02_traceSegment_085_2538_0013, g32p_row02_traceSegment_085_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2565 13 14, g32p_row02_traceSegment_085_2565_0013, g32p_row02_traceSegment_085_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2538 27 27, g32p_row02_traceSegment_085_2538_0027, g32p_row02_traceSegment_085_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2484 54 54, g32p_row02_traceSegment_085_2484_0054, g32p_row02_traceSegment_085_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2376 108 108, g32p_row02_traceSegment_085_2376_0108, g32p_row02_traceSegment_085_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_085 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2160 216 216, g32p_row02_traceSegment_085_2160_0216, g32p_row02_traceSegment_085_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_085 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1728 432 432, g32p_row02_traceSegment_085_1728_0432, g32p_row02_traceSegment_085_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2592 13 14, g32p_row02_traceSegment_085_2592_0013, g32p_row02_traceSegment_085_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2619 13 14, g32p_row02_traceSegment_085_2619_0013, g32p_row02_traceSegment_085_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2592 27 27, g32p_row02_traceSegment_085_2592_0027, g32p_row02_traceSegment_085_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2646 13 14, g32p_row02_traceSegment_085_2646_0013, g32p_row02_traceSegment_085_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2673 13 14, g32p_row02_traceSegment_085_2673_0013, g32p_row02_traceSegment_085_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2646 27 27, g32p_row02_traceSegment_085_2646_0027, g32p_row02_traceSegment_085_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2592 54 54, g32p_row02_traceSegment_085_2592_0054, g32p_row02_traceSegment_085_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2700 13 14, g32p_row02_traceSegment_085_2700_0013, g32p_row02_traceSegment_085_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2727 13 14, g32p_row02_traceSegment_085_2727_0013, g32p_row02_traceSegment_085_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2700 27 27, g32p_row02_traceSegment_085_2700_0027, g32p_row02_traceSegment_085_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2754 13 14, g32p_row02_traceSegment_085_2754_0013, g32p_row02_traceSegment_085_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2781 13 14, g32p_row02_traceSegment_085_2781_0013, g32p_row02_traceSegment_085_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2754 27 27, g32p_row02_traceSegment_085_2754_0027, g32p_row02_traceSegment_085_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2700 54 54, g32p_row02_traceSegment_085_2700_0054, g32p_row02_traceSegment_085_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2592 108 108, g32p_row02_traceSegment_085_2592_0108, g32p_row02_traceSegment_085_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2808 13 14, g32p_row02_traceSegment_085_2808_0013, g32p_row02_traceSegment_085_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2835 13 14, g32p_row02_traceSegment_085_2835_0013, g32p_row02_traceSegment_085_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2808 27 27, g32p_row02_traceSegment_085_2808_0027, g32p_row02_traceSegment_085_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2862 13 14, g32p_row02_traceSegment_085_2862_0013, g32p_row02_traceSegment_085_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2889 13 14, g32p_row02_traceSegment_085_2889_0013, g32p_row02_traceSegment_085_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2862 27 27, g32p_row02_traceSegment_085_2862_0027, g32p_row02_traceSegment_085_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2808 54 54, g32p_row02_traceSegment_085_2808_0054, g32p_row02_traceSegment_085_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2916 13 14, g32p_row02_traceSegment_085_2916_0013, g32p_row02_traceSegment_085_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2943 13 14, g32p_row02_traceSegment_085_2943_0013, g32p_row02_traceSegment_085_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2916 27 27, g32p_row02_traceSegment_085_2916_0027, g32p_row02_traceSegment_085_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2970 13 14, g32p_row02_traceSegment_085_2970_0013, g32p_row02_traceSegment_085_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2997 13 14, g32p_row02_traceSegment_085_2997_0013, g32p_row02_traceSegment_085_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2970 27 27, g32p_row02_traceSegment_085_2970_0027, g32p_row02_traceSegment_085_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2916 54 54, g32p_row02_traceSegment_085_2916_0054, g32p_row02_traceSegment_085_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2808 108 108, g32p_row02_traceSegment_085_2808_0108, g32p_row02_traceSegment_085_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_085 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2592 216 216, g32p_row02_traceSegment_085_2592_0216, g32p_row02_traceSegment_085_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3024 13 14, g32p_row02_traceSegment_085_3024_0013, g32p_row02_traceSegment_085_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3051 13 14, g32p_row02_traceSegment_085_3051_0013, g32p_row02_traceSegment_085_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3024 27 27, g32p_row02_traceSegment_085_3024_0027, g32p_row02_traceSegment_085_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3078 13 14, g32p_row02_traceSegment_085_3078_0013, g32p_row02_traceSegment_085_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3105 13 14, g32p_row02_traceSegment_085_3105_0013, g32p_row02_traceSegment_085_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3078 27 27, g32p_row02_traceSegment_085_3078_0027, g32p_row02_traceSegment_085_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3024 54 54, g32p_row02_traceSegment_085_3024_0054, g32p_row02_traceSegment_085_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3132 13 14, g32p_row02_traceSegment_085_3132_0013, g32p_row02_traceSegment_085_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3159 13 14, g32p_row02_traceSegment_085_3159_0013, g32p_row02_traceSegment_085_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3132 27 27, g32p_row02_traceSegment_085_3132_0027, g32p_row02_traceSegment_085_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3186 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3199 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3186 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3186 13 14, g32p_row02_traceSegment_085_3186_0013, g32p_row02_traceSegment_085_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3226 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3213 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3213 13 14, g32p_row02_traceSegment_085_3213_0013, g32p_row02_traceSegment_085_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 3186 54 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3186 27 27, g32p_row02_traceSegment_085_3186_0027, g32p_row02_traceSegment_085_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 3132 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3132 54 54, g32p_row02_traceSegment_085_3132_0054, g32p_row02_traceSegment_085_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 3024 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3024 108 108, g32p_row02_traceSegment_085_3024_0108, g32p_row02_traceSegment_085_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3253 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3240 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3240 13 14, g32p_row02_traceSegment_085_3240_0013, g32p_row02_traceSegment_085_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3280 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3267 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3267 13 14, g32p_row02_traceSegment_085_3267_0013, g32p_row02_traceSegment_085_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 3240 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3240 27 27, g32p_row02_traceSegment_085_3240_0027, g32p_row02_traceSegment_085_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3294 13 14, g32p_row02_traceSegment_085_3294_0013, g32p_row02_traceSegment_085_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3334 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3321 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3321 13 14, g32p_row02_traceSegment_085_3321_0013, g32p_row02_traceSegment_085_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 3294 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3294 27 27, g32p_row02_traceSegment_085_3294_0027, g32p_row02_traceSegment_085_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 3240 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3240 54 54, g32p_row02_traceSegment_085_3240_0054, g32p_row02_traceSegment_085_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3348 13 14, g32p_row02_traceSegment_085_3348_0013, g32p_row02_traceSegment_085_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3375 13 14, g32p_row02_traceSegment_085_3375_0013, g32p_row02_traceSegment_085_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3348 27 27, g32p_row02_traceSegment_085_3348_0027, g32p_row02_traceSegment_085_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3402 13 14, g32p_row02_traceSegment_085_3402_0013, g32p_row02_traceSegment_085_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_085 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_085 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_085_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_085 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3429 13 14, g32p_row02_traceSegment_085_3429_0013, g32p_row02_traceSegment_085_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_085 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3402 27 27, g32p_row02_traceSegment_085_3402_0027, g32p_row02_traceSegment_085_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_085 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3348 54 54, g32p_row02_traceSegment_085_3348_0054, g32p_row02_traceSegment_085_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_085 3240 216 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3240 108 108, g32p_row02_traceSegment_085_3240_0108, g32p_row02_traceSegment_085_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_085_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_085 3024 432 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 3024 216 216, g32p_row02_traceSegment_085_3024_0216, g32p_row02_traceSegment_085_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_085_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_085 2592 864 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 2592 432 432, g32p_row02_traceSegment_085_2592_0432, g32p_row02_traceSegment_085_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_085_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_085 1728 1728 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 1728 864 864, g32p_row02_traceSegment_085_1728_0864, g32p_row02_traceSegment_085_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_085_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_085 0 3456 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_085 0 1728 1728, g32p_row02_traceSegment_085_0000_1728, g32p_row02_traceSegment_085_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 85 = [0, 0, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_085_0000_3456

end HodgeLean.Foundations.Program

end
end
