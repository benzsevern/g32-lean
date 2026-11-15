import HodgeLean.Foundations.Program.G32PropFourSixPacked0335
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0341

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_083 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 83 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_083_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 0 13 14, g32p_row04_traceSegment_083_0000_0013, g32p_row04_traceSegment_083_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 27 13 14, g32p_row04_traceSegment_083_0027_0013, g32p_row04_traceSegment_083_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 0 27 27, g32p_row04_traceSegment_083_0000_0027, g32p_row04_traceSegment_083_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 54 13 14, g32p_row04_traceSegment_083_0054_0013, g32p_row04_traceSegment_083_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 81 13 14, g32p_row04_traceSegment_083_0081_0013, g32p_row04_traceSegment_083_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 54 27 27, g32p_row04_traceSegment_083_0054_0027, g32p_row04_traceSegment_083_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 0 54 54, g32p_row04_traceSegment_083_0000_0054, g32p_row04_traceSegment_083_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 108 13 14, g32p_row04_traceSegment_083_0108_0013, g32p_row04_traceSegment_083_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 135 13 14, g32p_row04_traceSegment_083_0135_0013, g32p_row04_traceSegment_083_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 108 27 27, g32p_row04_traceSegment_083_0108_0027, g32p_row04_traceSegment_083_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 162 13 14, g32p_row04_traceSegment_083_0162_0013, g32p_row04_traceSegment_083_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 189 13 14, g32p_row04_traceSegment_083_0189_0013, g32p_row04_traceSegment_083_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 162 27 27, g32p_row04_traceSegment_083_0162_0027, g32p_row04_traceSegment_083_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 108 54 54, g32p_row04_traceSegment_083_0108_0054, g32p_row04_traceSegment_083_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_083 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 0 108 108, g32p_row04_traceSegment_083_0000_0108, g32p_row04_traceSegment_083_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 216 13 14, g32p_row04_traceSegment_083_0216_0013, g32p_row04_traceSegment_083_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 243 13 14, g32p_row04_traceSegment_083_0243_0013, g32p_row04_traceSegment_083_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 216 27 27, g32p_row04_traceSegment_083_0216_0027, g32p_row04_traceSegment_083_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 270 13 14, g32p_row04_traceSegment_083_0270_0013, g32p_row04_traceSegment_083_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 297 13 14, g32p_row04_traceSegment_083_0297_0013, g32p_row04_traceSegment_083_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 270 27 27, g32p_row04_traceSegment_083_0270_0027, g32p_row04_traceSegment_083_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 216 54 54, g32p_row04_traceSegment_083_0216_0054, g32p_row04_traceSegment_083_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 324 13 14, g32p_row04_traceSegment_083_0324_0013, g32p_row04_traceSegment_083_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 351 13 14, g32p_row04_traceSegment_083_0351_0013, g32p_row04_traceSegment_083_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 324 27 27, g32p_row04_traceSegment_083_0324_0027, g32p_row04_traceSegment_083_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 378 13 14, g32p_row04_traceSegment_083_0378_0013, g32p_row04_traceSegment_083_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 405 13 14, g32p_row04_traceSegment_083_0405_0013, g32p_row04_traceSegment_083_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 378 27 27, g32p_row04_traceSegment_083_0378_0027, g32p_row04_traceSegment_083_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 324 54 54, g32p_row04_traceSegment_083_0324_0054, g32p_row04_traceSegment_083_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_083 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 216 108 108, g32p_row04_traceSegment_083_0216_0108, g32p_row04_traceSegment_083_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_083 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 0 216 216, g32p_row04_traceSegment_083_0000_0216, g32p_row04_traceSegment_083_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 432 13 14, g32p_row04_traceSegment_083_0432_0013, g32p_row04_traceSegment_083_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 459 13 14, g32p_row04_traceSegment_083_0459_0013, g32p_row04_traceSegment_083_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 432 27 27, g32p_row04_traceSegment_083_0432_0027, g32p_row04_traceSegment_083_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 486 13 14, g32p_row04_traceSegment_083_0486_0013, g32p_row04_traceSegment_083_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 513 13 14, g32p_row04_traceSegment_083_0513_0013, g32p_row04_traceSegment_083_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 486 27 27, g32p_row04_traceSegment_083_0486_0027, g32p_row04_traceSegment_083_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 432 54 54, g32p_row04_traceSegment_083_0432_0054, g32p_row04_traceSegment_083_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 540 13 14, g32p_row04_traceSegment_083_0540_0013, g32p_row04_traceSegment_083_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 567 13 14, g32p_row04_traceSegment_083_0567_0013, g32p_row04_traceSegment_083_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 540 27 27, g32p_row04_traceSegment_083_0540_0027, g32p_row04_traceSegment_083_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 594 13 14, g32p_row04_traceSegment_083_0594_0013, g32p_row04_traceSegment_083_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 621 13 14, g32p_row04_traceSegment_083_0621_0013, g32p_row04_traceSegment_083_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 594 27 27, g32p_row04_traceSegment_083_0594_0027, g32p_row04_traceSegment_083_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 540 54 54, g32p_row04_traceSegment_083_0540_0054, g32p_row04_traceSegment_083_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_083 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 432 108 108, g32p_row04_traceSegment_083_0432_0108, g32p_row04_traceSegment_083_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 648 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 661 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 648 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 648 13 14, g32p_row04_traceSegment_083_0648_0013, g32p_row04_traceSegment_083_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 675 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 675 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 675 13 14, g32p_row04_traceSegment_083_0675_0013, g32p_row04_traceSegment_083_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 648 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 648 27 27, g32p_row04_traceSegment_083_0648_0027, g32p_row04_traceSegment_083_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 715 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 702 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 702 13 14, g32p_row04_traceSegment_083_0702_0013, g32p_row04_traceSegment_083_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 729 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 729 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 729 13 14, g32p_row04_traceSegment_083_0729_0013, g32p_row04_traceSegment_083_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 702 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 702 27 27, g32p_row04_traceSegment_083_0702_0027, g32p_row04_traceSegment_083_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 648 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 648 54 54, g32p_row04_traceSegment_083_0648_0054, g32p_row04_traceSegment_083_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 756 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 756 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 756 13 14, g32p_row04_traceSegment_083_0756_0013, g32p_row04_traceSegment_083_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 783 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 783 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 783 13 14, g32p_row04_traceSegment_083_0783_0013, g32p_row04_traceSegment_083_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 756 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 756 27 27, g32p_row04_traceSegment_083_0756_0027, g32p_row04_traceSegment_083_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 810 13 14, g32p_row04_traceSegment_083_0810_0013, g32p_row04_traceSegment_083_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 837 13 14, g32p_row04_traceSegment_083_0837_0013, g32p_row04_traceSegment_083_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 810 27 27, g32p_row04_traceSegment_083_0810_0027, g32p_row04_traceSegment_083_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 756 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 756 54 54, g32p_row04_traceSegment_083_0756_0054, g32p_row04_traceSegment_083_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_083 648 216 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 648 108 108, g32p_row04_traceSegment_083_0648_0108, g32p_row04_traceSegment_083_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_083 432 432 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 432 216 216, g32p_row04_traceSegment_083_0432_0216, g32p_row04_traceSegment_083_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_083 0 864 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 0 432 432, g32p_row04_traceSegment_083_0000_0432, g32p_row04_traceSegment_083_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 864 13 14, g32p_row04_traceSegment_083_0864_0013, g32p_row04_traceSegment_083_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 891 13 14, g32p_row04_traceSegment_083_0891_0013, g32p_row04_traceSegment_083_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 864 27 27, g32p_row04_traceSegment_083_0864_0027, g32p_row04_traceSegment_083_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 918 13 14, g32p_row04_traceSegment_083_0918_0013, g32p_row04_traceSegment_083_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 945 13 14, g32p_row04_traceSegment_083_0945_0013, g32p_row04_traceSegment_083_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 918 27 27, g32p_row04_traceSegment_083_0918_0027, g32p_row04_traceSegment_083_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 864 54 54, g32p_row04_traceSegment_083_0864_0054, g32p_row04_traceSegment_083_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 972 13 14, g32p_row04_traceSegment_083_0972_0013, g32p_row04_traceSegment_083_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 999 13 14, g32p_row04_traceSegment_083_0999_0013, g32p_row04_traceSegment_083_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 972 27 27, g32p_row04_traceSegment_083_0972_0027, g32p_row04_traceSegment_083_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1026 13 14, g32p_row04_traceSegment_083_1026_0013, g32p_row04_traceSegment_083_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1053 13 14, g32p_row04_traceSegment_083_1053_0013, g32p_row04_traceSegment_083_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1026 27 27, g32p_row04_traceSegment_083_1026_0027, g32p_row04_traceSegment_083_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 972 54 54, g32p_row04_traceSegment_083_0972_0054, g32p_row04_traceSegment_083_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_083 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 864 108 108, g32p_row04_traceSegment_083_0864_0108, g32p_row04_traceSegment_083_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1080 13 14, g32p_row04_traceSegment_083_1080_0013, g32p_row04_traceSegment_083_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1107 13 14, g32p_row04_traceSegment_083_1107_0013, g32p_row04_traceSegment_083_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1080 27 27, g32p_row04_traceSegment_083_1080_0027, g32p_row04_traceSegment_083_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1134 13 14, g32p_row04_traceSegment_083_1134_0013, g32p_row04_traceSegment_083_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1161 13 14, g32p_row04_traceSegment_083_1161_0013, g32p_row04_traceSegment_083_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1134 27 27, g32p_row04_traceSegment_083_1134_0027, g32p_row04_traceSegment_083_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1080 54 54, g32p_row04_traceSegment_083_1080_0054, g32p_row04_traceSegment_083_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1188 13 14, g32p_row04_traceSegment_083_1188_0013, g32p_row04_traceSegment_083_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1215 13 14, g32p_row04_traceSegment_083_1215_0013, g32p_row04_traceSegment_083_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1188 27 27, g32p_row04_traceSegment_083_1188_0027, g32p_row04_traceSegment_083_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1242 13 14, g32p_row04_traceSegment_083_1242_0013, g32p_row04_traceSegment_083_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1269 13 14, g32p_row04_traceSegment_083_1269_0013, g32p_row04_traceSegment_083_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1242 27 27, g32p_row04_traceSegment_083_1242_0027, g32p_row04_traceSegment_083_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1188 54 54, g32p_row04_traceSegment_083_1188_0054, g32p_row04_traceSegment_083_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_083 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1080 108 108, g32p_row04_traceSegment_083_1080_0108, g32p_row04_traceSegment_083_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_083 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 864 216 216, g32p_row04_traceSegment_083_0864_0216, g32p_row04_traceSegment_083_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1296 13 14, g32p_row04_traceSegment_083_1296_0013, g32p_row04_traceSegment_083_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1323 13 14, g32p_row04_traceSegment_083_1323_0013, g32p_row04_traceSegment_083_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1296 27 27, g32p_row04_traceSegment_083_1296_0027, g32p_row04_traceSegment_083_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1350 13 14, g32p_row04_traceSegment_083_1350_0013, g32p_row04_traceSegment_083_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1377 13 14, g32p_row04_traceSegment_083_1377_0013, g32p_row04_traceSegment_083_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1350 27 27, g32p_row04_traceSegment_083_1350_0027, g32p_row04_traceSegment_083_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1296 54 54, g32p_row04_traceSegment_083_1296_0054, g32p_row04_traceSegment_083_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1404 13 14, g32p_row04_traceSegment_083_1404_0013, g32p_row04_traceSegment_083_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1431 13 14, g32p_row04_traceSegment_083_1431_0013, g32p_row04_traceSegment_083_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1404 27 27, g32p_row04_traceSegment_083_1404_0027, g32p_row04_traceSegment_083_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1458 13 14, g32p_row04_traceSegment_083_1458_0013, g32p_row04_traceSegment_083_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1485 13 14, g32p_row04_traceSegment_083_1485_0013, g32p_row04_traceSegment_083_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1458 27 27, g32p_row04_traceSegment_083_1458_0027, g32p_row04_traceSegment_083_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1404 54 54, g32p_row04_traceSegment_083_1404_0054, g32p_row04_traceSegment_083_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_083 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1296 108 108, g32p_row04_traceSegment_083_1296_0108, g32p_row04_traceSegment_083_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1512 13 14, g32p_row04_traceSegment_083_1512_0013, g32p_row04_traceSegment_083_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1539 13 14, g32p_row04_traceSegment_083_1539_0013, g32p_row04_traceSegment_083_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1512 27 27, g32p_row04_traceSegment_083_1512_0027, g32p_row04_traceSegment_083_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1566 13 14, g32p_row04_traceSegment_083_1566_0013, g32p_row04_traceSegment_083_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1593 13 14, g32p_row04_traceSegment_083_1593_0013, g32p_row04_traceSegment_083_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1566 27 27, g32p_row04_traceSegment_083_1566_0027, g32p_row04_traceSegment_083_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1512 54 54, g32p_row04_traceSegment_083_1512_0054, g32p_row04_traceSegment_083_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1620 13 14, g32p_row04_traceSegment_083_1620_0013, g32p_row04_traceSegment_083_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1647 13 14, g32p_row04_traceSegment_083_1647_0013, g32p_row04_traceSegment_083_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1620 27 27, g32p_row04_traceSegment_083_1620_0027, g32p_row04_traceSegment_083_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1674 13 14, g32p_row04_traceSegment_083_1674_0013, g32p_row04_traceSegment_083_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_083 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_083 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_083_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_083 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1701 13 14, g32p_row04_traceSegment_083_1701_0013, g32p_row04_traceSegment_083_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_083 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1674 27 27, g32p_row04_traceSegment_083_1674_0027, g32p_row04_traceSegment_083_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_083 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1620 54 54, g32p_row04_traceSegment_083_1620_0054, g32p_row04_traceSegment_083_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_083 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1512 108 108, g32p_row04_traceSegment_083_1512_0108, g32p_row04_traceSegment_083_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_083_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_083 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 1296 216 216, g32p_row04_traceSegment_083_1296_0216, g32p_row04_traceSegment_083_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_083 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 864 432 432, g32p_row04_traceSegment_083_0864_0432, g32p_row04_traceSegment_083_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_083_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_083 0 1728 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_083 0 864 864, g32p_row04_traceSegment_083_0000_0864, g32p_row04_traceSegment_083_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 83 = [0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_083_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_084 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 84 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_084_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 0 13 14, g32p_row04_traceSegment_084_0000_0013, g32p_row04_traceSegment_084_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 27 13 14, g32p_row04_traceSegment_084_0027_0013, g32p_row04_traceSegment_084_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 0 27 27, g32p_row04_traceSegment_084_0000_0027, g32p_row04_traceSegment_084_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 54 13 14, g32p_row04_traceSegment_084_0054_0013, g32p_row04_traceSegment_084_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 81 13 14, g32p_row04_traceSegment_084_0081_0013, g32p_row04_traceSegment_084_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 54 27 27, g32p_row04_traceSegment_084_0054_0027, g32p_row04_traceSegment_084_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 0 54 54, g32p_row04_traceSegment_084_0000_0054, g32p_row04_traceSegment_084_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 108 13 14, g32p_row04_traceSegment_084_0108_0013, g32p_row04_traceSegment_084_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 135 13 14, g32p_row04_traceSegment_084_0135_0013, g32p_row04_traceSegment_084_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 108 27 27, g32p_row04_traceSegment_084_0108_0027, g32p_row04_traceSegment_084_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 162 13 14, g32p_row04_traceSegment_084_0162_0013, g32p_row04_traceSegment_084_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 189 13 14, g32p_row04_traceSegment_084_0189_0013, g32p_row04_traceSegment_084_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 162 27 27, g32p_row04_traceSegment_084_0162_0027, g32p_row04_traceSegment_084_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 108 54 54, g32p_row04_traceSegment_084_0108_0054, g32p_row04_traceSegment_084_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_084 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 0 108 108, g32p_row04_traceSegment_084_0000_0108, g32p_row04_traceSegment_084_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 216 13 14, g32p_row04_traceSegment_084_0216_0013, g32p_row04_traceSegment_084_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 243 13 14, g32p_row04_traceSegment_084_0243_0013, g32p_row04_traceSegment_084_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 216 27 27, g32p_row04_traceSegment_084_0216_0027, g32p_row04_traceSegment_084_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 270 13 14, g32p_row04_traceSegment_084_0270_0013, g32p_row04_traceSegment_084_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 297 13 14, g32p_row04_traceSegment_084_0297_0013, g32p_row04_traceSegment_084_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 270 27 27, g32p_row04_traceSegment_084_0270_0027, g32p_row04_traceSegment_084_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 216 54 54, g32p_row04_traceSegment_084_0216_0054, g32p_row04_traceSegment_084_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 324 13 14, g32p_row04_traceSegment_084_0324_0013, g32p_row04_traceSegment_084_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 351 13 14, g32p_row04_traceSegment_084_0351_0013, g32p_row04_traceSegment_084_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 324 27 27, g32p_row04_traceSegment_084_0324_0027, g32p_row04_traceSegment_084_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 378 13 14, g32p_row04_traceSegment_084_0378_0013, g32p_row04_traceSegment_084_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 405 13 14, g32p_row04_traceSegment_084_0405_0013, g32p_row04_traceSegment_084_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 378 27 27, g32p_row04_traceSegment_084_0378_0027, g32p_row04_traceSegment_084_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 324 54 54, g32p_row04_traceSegment_084_0324_0054, g32p_row04_traceSegment_084_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_084 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 216 108 108, g32p_row04_traceSegment_084_0216_0108, g32p_row04_traceSegment_084_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_084 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 0 216 216, g32p_row04_traceSegment_084_0000_0216, g32p_row04_traceSegment_084_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 432 13 14, g32p_row04_traceSegment_084_0432_0013, g32p_row04_traceSegment_084_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 459 13 14, g32p_row04_traceSegment_084_0459_0013, g32p_row04_traceSegment_084_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 432 27 27, g32p_row04_traceSegment_084_0432_0027, g32p_row04_traceSegment_084_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 499 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 486 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 486 13 14, g32p_row04_traceSegment_084_0486_0013, g32p_row04_traceSegment_084_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 513 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 513 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 513 13 14, g32p_row04_traceSegment_084_0513_0013, g32p_row04_traceSegment_084_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 486 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 486 27 27, g32p_row04_traceSegment_084_0486_0027, g32p_row04_traceSegment_084_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 432 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 432 54 54, g32p_row04_traceSegment_084_0432_0054, g32p_row04_traceSegment_084_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 553 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 540 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 540 13 14, g32p_row04_traceSegment_084_0540_0013, g32p_row04_traceSegment_084_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 567 13 14, g32p_row04_traceSegment_084_0567_0013, g32p_row04_traceSegment_084_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 540 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 540 27 27, g32p_row04_traceSegment_084_0540_0027, g32p_row04_traceSegment_084_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 594 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 607 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 594 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 594 13 14, g32p_row04_traceSegment_084_0594_0013, g32p_row04_traceSegment_084_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 621 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 634 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 621 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 621 13 14, g32p_row04_traceSegment_084_0621_0013, g32p_row04_traceSegment_084_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 594 54 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 594 27 27, g32p_row04_traceSegment_084_0594_0027, g32p_row04_traceSegment_084_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 540 108 = [3, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 540 54 54, g32p_row04_traceSegment_084_0540_0054, g32p_row04_traceSegment_084_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_084 432 216 = [3, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 432 108 108, g32p_row04_traceSegment_084_0432_0108, g32p_row04_traceSegment_084_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 661 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 648 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 648 13 14, g32p_row04_traceSegment_084_0648_0013, g32p_row04_traceSegment_084_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 675 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 688 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 675 27 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 675 13 14, g32p_row04_traceSegment_084_0675_0013, g32p_row04_traceSegment_084_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 648 54 = [1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 648 27 27, g32p_row04_traceSegment_084_0648_0027, g32p_row04_traceSegment_084_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 715 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 702 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 702 13 14, g32p_row04_traceSegment_084_0702_0013, g32p_row04_traceSegment_084_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 729 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 729 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 729 13 14, g32p_row04_traceSegment_084_0729_0013, g32p_row04_traceSegment_084_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 702 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 702 27 27, g32p_row04_traceSegment_084_0702_0027, g32p_row04_traceSegment_084_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 648 108 = [1, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 648 54 54, g32p_row04_traceSegment_084_0648_0054, g32p_row04_traceSegment_084_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 756 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 756 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 756 13 14, g32p_row04_traceSegment_084_0756_0013, g32p_row04_traceSegment_084_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 783 13 14, g32p_row04_traceSegment_084_0783_0013, g32p_row04_traceSegment_084_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 756 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 756 27 27, g32p_row04_traceSegment_084_0756_0027, g32p_row04_traceSegment_084_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 810 13 14, g32p_row04_traceSegment_084_0810_0013, g32p_row04_traceSegment_084_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 837 13 14, g32p_row04_traceSegment_084_0837_0013, g32p_row04_traceSegment_084_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 810 27 27, g32p_row04_traceSegment_084_0810_0027, g32p_row04_traceSegment_084_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 756 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 756 54 54, g32p_row04_traceSegment_084_0756_0054, g32p_row04_traceSegment_084_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_084 648 216 = [1, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 648 108 108, g32p_row04_traceSegment_084_0648_0108, g32p_row04_traceSegment_084_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_084 432 432 = [4, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 432 216 216, g32p_row04_traceSegment_084_0432_0216, g32p_row04_traceSegment_084_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_084 0 864 = [4, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 0 432 432, g32p_row04_traceSegment_084_0000_0432, g32p_row04_traceSegment_084_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 864 13 14, g32p_row04_traceSegment_084_0864_0013, g32p_row04_traceSegment_084_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 891 13 14, g32p_row04_traceSegment_084_0891_0013, g32p_row04_traceSegment_084_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 864 27 27, g32p_row04_traceSegment_084_0864_0027, g32p_row04_traceSegment_084_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 918 13 14, g32p_row04_traceSegment_084_0918_0013, g32p_row04_traceSegment_084_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 945 13 14, g32p_row04_traceSegment_084_0945_0013, g32p_row04_traceSegment_084_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 918 27 27, g32p_row04_traceSegment_084_0918_0027, g32p_row04_traceSegment_084_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 864 54 54, g32p_row04_traceSegment_084_0864_0054, g32p_row04_traceSegment_084_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 972 13 14, g32p_row04_traceSegment_084_0972_0013, g32p_row04_traceSegment_084_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 999 13 14, g32p_row04_traceSegment_084_0999_0013, g32p_row04_traceSegment_084_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 972 27 27, g32p_row04_traceSegment_084_0972_0027, g32p_row04_traceSegment_084_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1026 13 14, g32p_row04_traceSegment_084_1026_0013, g32p_row04_traceSegment_084_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1053 13 14, g32p_row04_traceSegment_084_1053_0013, g32p_row04_traceSegment_084_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1026 27 27, g32p_row04_traceSegment_084_1026_0027, g32p_row04_traceSegment_084_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 972 54 54, g32p_row04_traceSegment_084_0972_0054, g32p_row04_traceSegment_084_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_084 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 864 108 108, g32p_row04_traceSegment_084_0864_0108, g32p_row04_traceSegment_084_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1080 13 14, g32p_row04_traceSegment_084_1080_0013, g32p_row04_traceSegment_084_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1107 13 14, g32p_row04_traceSegment_084_1107_0013, g32p_row04_traceSegment_084_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1080 27 27, g32p_row04_traceSegment_084_1080_0027, g32p_row04_traceSegment_084_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1134 13 14, g32p_row04_traceSegment_084_1134_0013, g32p_row04_traceSegment_084_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1161 13 14, g32p_row04_traceSegment_084_1161_0013, g32p_row04_traceSegment_084_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1134 27 27, g32p_row04_traceSegment_084_1134_0027, g32p_row04_traceSegment_084_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1080 54 54, g32p_row04_traceSegment_084_1080_0054, g32p_row04_traceSegment_084_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1188 13 14, g32p_row04_traceSegment_084_1188_0013, g32p_row04_traceSegment_084_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1215 13 14, g32p_row04_traceSegment_084_1215_0013, g32p_row04_traceSegment_084_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1188 27 27, g32p_row04_traceSegment_084_1188_0027, g32p_row04_traceSegment_084_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1242 13 14, g32p_row04_traceSegment_084_1242_0013, g32p_row04_traceSegment_084_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1269 13 14, g32p_row04_traceSegment_084_1269_0013, g32p_row04_traceSegment_084_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1242 27 27, g32p_row04_traceSegment_084_1242_0027, g32p_row04_traceSegment_084_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1188 54 54, g32p_row04_traceSegment_084_1188_0054, g32p_row04_traceSegment_084_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_084 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1080 108 108, g32p_row04_traceSegment_084_1080_0108, g32p_row04_traceSegment_084_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_084 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 864 216 216, g32p_row04_traceSegment_084_0864_0216, g32p_row04_traceSegment_084_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1296 13 14, g32p_row04_traceSegment_084_1296_0013, g32p_row04_traceSegment_084_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1323 13 14, g32p_row04_traceSegment_084_1323_0013, g32p_row04_traceSegment_084_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1296 27 27, g32p_row04_traceSegment_084_1296_0027, g32p_row04_traceSegment_084_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1350 13 14, g32p_row04_traceSegment_084_1350_0013, g32p_row04_traceSegment_084_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1377 13 14, g32p_row04_traceSegment_084_1377_0013, g32p_row04_traceSegment_084_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1350 27 27, g32p_row04_traceSegment_084_1350_0027, g32p_row04_traceSegment_084_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1296 54 54, g32p_row04_traceSegment_084_1296_0054, g32p_row04_traceSegment_084_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1404 13 14, g32p_row04_traceSegment_084_1404_0013, g32p_row04_traceSegment_084_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1431 13 14, g32p_row04_traceSegment_084_1431_0013, g32p_row04_traceSegment_084_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1404 27 27, g32p_row04_traceSegment_084_1404_0027, g32p_row04_traceSegment_084_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1458 13 14, g32p_row04_traceSegment_084_1458_0013, g32p_row04_traceSegment_084_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1485 13 14, g32p_row04_traceSegment_084_1485_0013, g32p_row04_traceSegment_084_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1458 27 27, g32p_row04_traceSegment_084_1458_0027, g32p_row04_traceSegment_084_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1404 54 54, g32p_row04_traceSegment_084_1404_0054, g32p_row04_traceSegment_084_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_084 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1296 108 108, g32p_row04_traceSegment_084_1296_0108, g32p_row04_traceSegment_084_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1512 13 14, g32p_row04_traceSegment_084_1512_0013, g32p_row04_traceSegment_084_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1552 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1539 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1539 13 14, g32p_row04_traceSegment_084_1539_0013, g32p_row04_traceSegment_084_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1512 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1512 27 27, g32p_row04_traceSegment_084_1512_0027, g32p_row04_traceSegment_084_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1566 13 14, g32p_row04_traceSegment_084_1566_0013, g32p_row04_traceSegment_084_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1593 13 14, g32p_row04_traceSegment_084_1593_0013, g32p_row04_traceSegment_084_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1566 27 27, g32p_row04_traceSegment_084_1566_0027, g32p_row04_traceSegment_084_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 1512 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1512 54 54, g32p_row04_traceSegment_084_1512_0054, g32p_row04_traceSegment_084_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1620 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1633 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1620 27 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1620 13 14, g32p_row04_traceSegment_084_1620_0013, g32p_row04_traceSegment_084_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1647 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1660 14 = [4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1647 27 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1647 13 14, g32p_row04_traceSegment_084_1647_0013, g32p_row04_traceSegment_084_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1620 54 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1620 27 27, g32p_row04_traceSegment_084_1620_0027, g32p_row04_traceSegment_084_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1674 13 14, g32p_row04_traceSegment_084_1674_0013, g32p_row04_traceSegment_084_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_084 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_084 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_084_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_084 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1701 13 14, g32p_row04_traceSegment_084_1701_0013, g32p_row04_traceSegment_084_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_084 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1674 27 27, g32p_row04_traceSegment_084_1674_0027, g32p_row04_traceSegment_084_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_084 1620 108 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1620 54 54, g32p_row04_traceSegment_084_1620_0054, g32p_row04_traceSegment_084_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_084 1512 216 = [12, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1512 108 108, g32p_row04_traceSegment_084_1512_0108, g32p_row04_traceSegment_084_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_084_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_084 1296 432 = [12, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 1296 216 216, g32p_row04_traceSegment_084_1296_0216, g32p_row04_traceSegment_084_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_084 864 864 = [12, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 864 432 432, g32p_row04_traceSegment_084_0864_0432, g32p_row04_traceSegment_084_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_084_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_084 0 1728 = [16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_084 0 864 864, g32p_row04_traceSegment_084_0000_0864, g32p_row04_traceSegment_084_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 84 = [16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_084_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_085 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 85 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_085_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 0 13 14, g32p_row04_traceSegment_085_0000_0013, g32p_row04_traceSegment_085_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 27 13 14, g32p_row04_traceSegment_085_0027_0013, g32p_row04_traceSegment_085_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 0 27 27, g32p_row04_traceSegment_085_0000_0027, g32p_row04_traceSegment_085_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 54 13 14, g32p_row04_traceSegment_085_0054_0013, g32p_row04_traceSegment_085_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 81 13 14, g32p_row04_traceSegment_085_0081_0013, g32p_row04_traceSegment_085_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 54 27 27, g32p_row04_traceSegment_085_0054_0027, g32p_row04_traceSegment_085_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 0 54 54, g32p_row04_traceSegment_085_0000_0054, g32p_row04_traceSegment_085_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 108 13 14, g32p_row04_traceSegment_085_0108_0013, g32p_row04_traceSegment_085_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 135 13 14, g32p_row04_traceSegment_085_0135_0013, g32p_row04_traceSegment_085_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 108 27 27, g32p_row04_traceSegment_085_0108_0027, g32p_row04_traceSegment_085_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 162 13 14, g32p_row04_traceSegment_085_0162_0013, g32p_row04_traceSegment_085_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 189 13 14, g32p_row04_traceSegment_085_0189_0013, g32p_row04_traceSegment_085_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 162 27 27, g32p_row04_traceSegment_085_0162_0027, g32p_row04_traceSegment_085_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 108 54 54, g32p_row04_traceSegment_085_0108_0054, g32p_row04_traceSegment_085_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_085 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 0 108 108, g32p_row04_traceSegment_085_0000_0108, g32p_row04_traceSegment_085_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 216 13 14, g32p_row04_traceSegment_085_0216_0013, g32p_row04_traceSegment_085_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 243 13 14, g32p_row04_traceSegment_085_0243_0013, g32p_row04_traceSegment_085_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 216 27 27, g32p_row04_traceSegment_085_0216_0027, g32p_row04_traceSegment_085_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 270 13 14, g32p_row04_traceSegment_085_0270_0013, g32p_row04_traceSegment_085_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 297 13 14, g32p_row04_traceSegment_085_0297_0013, g32p_row04_traceSegment_085_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 270 27 27, g32p_row04_traceSegment_085_0270_0027, g32p_row04_traceSegment_085_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 216 54 54, g32p_row04_traceSegment_085_0216_0054, g32p_row04_traceSegment_085_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 324 13 14, g32p_row04_traceSegment_085_0324_0013, g32p_row04_traceSegment_085_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 351 13 14, g32p_row04_traceSegment_085_0351_0013, g32p_row04_traceSegment_085_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 324 27 27, g32p_row04_traceSegment_085_0324_0027, g32p_row04_traceSegment_085_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 378 13 14, g32p_row04_traceSegment_085_0378_0013, g32p_row04_traceSegment_085_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 405 13 14, g32p_row04_traceSegment_085_0405_0013, g32p_row04_traceSegment_085_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 378 27 27, g32p_row04_traceSegment_085_0378_0027, g32p_row04_traceSegment_085_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 324 54 54, g32p_row04_traceSegment_085_0324_0054, g32p_row04_traceSegment_085_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_085 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 216 108 108, g32p_row04_traceSegment_085_0216_0108, g32p_row04_traceSegment_085_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_085 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 0 216 216, g32p_row04_traceSegment_085_0000_0216, g32p_row04_traceSegment_085_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 432 13 14, g32p_row04_traceSegment_085_0432_0013, g32p_row04_traceSegment_085_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 459 13 14, g32p_row04_traceSegment_085_0459_0013, g32p_row04_traceSegment_085_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 432 27 27, g32p_row04_traceSegment_085_0432_0027, g32p_row04_traceSegment_085_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 486 13 14, g32p_row04_traceSegment_085_0486_0013, g32p_row04_traceSegment_085_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 513 13 14, g32p_row04_traceSegment_085_0513_0013, g32p_row04_traceSegment_085_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 486 27 27, g32p_row04_traceSegment_085_0486_0027, g32p_row04_traceSegment_085_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 432 54 54, g32p_row04_traceSegment_085_0432_0054, g32p_row04_traceSegment_085_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 540 13 14, g32p_row04_traceSegment_085_0540_0013, g32p_row04_traceSegment_085_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 567 13 14, g32p_row04_traceSegment_085_0567_0013, g32p_row04_traceSegment_085_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 540 27 27, g32p_row04_traceSegment_085_0540_0027, g32p_row04_traceSegment_085_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 594 13 14, g32p_row04_traceSegment_085_0594_0013, g32p_row04_traceSegment_085_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 621 13 14, g32p_row04_traceSegment_085_0621_0013, g32p_row04_traceSegment_085_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 594 27 27, g32p_row04_traceSegment_085_0594_0027, g32p_row04_traceSegment_085_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 540 54 54, g32p_row04_traceSegment_085_0540_0054, g32p_row04_traceSegment_085_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_085 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 432 108 108, g32p_row04_traceSegment_085_0432_0108, g32p_row04_traceSegment_085_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 648 13 14, g32p_row04_traceSegment_085_0648_0013, g32p_row04_traceSegment_085_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 675 13 14, g32p_row04_traceSegment_085_0675_0013, g32p_row04_traceSegment_085_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 648 27 27, g32p_row04_traceSegment_085_0648_0027, g32p_row04_traceSegment_085_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 702 13 14, g32p_row04_traceSegment_085_0702_0013, g32p_row04_traceSegment_085_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 729 13 14, g32p_row04_traceSegment_085_0729_0013, g32p_row04_traceSegment_085_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 702 27 27, g32p_row04_traceSegment_085_0702_0027, g32p_row04_traceSegment_085_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 648 54 54, g32p_row04_traceSegment_085_0648_0054, g32p_row04_traceSegment_085_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 756 13 14, g32p_row04_traceSegment_085_0756_0013, g32p_row04_traceSegment_085_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 783 13 14, g32p_row04_traceSegment_085_0783_0013, g32p_row04_traceSegment_085_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 756 27 27, g32p_row04_traceSegment_085_0756_0027, g32p_row04_traceSegment_085_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 810 13 14, g32p_row04_traceSegment_085_0810_0013, g32p_row04_traceSegment_085_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 837 13 14, g32p_row04_traceSegment_085_0837_0013, g32p_row04_traceSegment_085_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 810 27 27, g32p_row04_traceSegment_085_0810_0027, g32p_row04_traceSegment_085_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 756 54 54, g32p_row04_traceSegment_085_0756_0054, g32p_row04_traceSegment_085_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_085 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 648 108 108, g32p_row04_traceSegment_085_0648_0108, g32p_row04_traceSegment_085_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_085 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 432 216 216, g32p_row04_traceSegment_085_0432_0216, g32p_row04_traceSegment_085_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_085 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 0 432 432, g32p_row04_traceSegment_085_0000_0432, g32p_row04_traceSegment_085_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 864 13 14, g32p_row04_traceSegment_085_0864_0013, g32p_row04_traceSegment_085_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 891 13 14, g32p_row04_traceSegment_085_0891_0013, g32p_row04_traceSegment_085_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 864 27 27, g32p_row04_traceSegment_085_0864_0027, g32p_row04_traceSegment_085_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 918 13 14, g32p_row04_traceSegment_085_0918_0013, g32p_row04_traceSegment_085_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 945 13 14, g32p_row04_traceSegment_085_0945_0013, g32p_row04_traceSegment_085_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 918 27 27, g32p_row04_traceSegment_085_0918_0027, g32p_row04_traceSegment_085_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 864 54 54, g32p_row04_traceSegment_085_0864_0054, g32p_row04_traceSegment_085_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 972 13 14, g32p_row04_traceSegment_085_0972_0013, g32p_row04_traceSegment_085_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 999 13 14, g32p_row04_traceSegment_085_0999_0013, g32p_row04_traceSegment_085_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 972 27 27, g32p_row04_traceSegment_085_0972_0027, g32p_row04_traceSegment_085_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1026 13 14, g32p_row04_traceSegment_085_1026_0013, g32p_row04_traceSegment_085_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1053 13 14, g32p_row04_traceSegment_085_1053_0013, g32p_row04_traceSegment_085_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1026 27 27, g32p_row04_traceSegment_085_1026_0027, g32p_row04_traceSegment_085_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 972 54 54, g32p_row04_traceSegment_085_0972_0054, g32p_row04_traceSegment_085_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_085 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 864 108 108, g32p_row04_traceSegment_085_0864_0108, g32p_row04_traceSegment_085_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1080 13 14, g32p_row04_traceSegment_085_1080_0013, g32p_row04_traceSegment_085_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1107 13 14, g32p_row04_traceSegment_085_1107_0013, g32p_row04_traceSegment_085_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1080 27 27, g32p_row04_traceSegment_085_1080_0027, g32p_row04_traceSegment_085_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1134 13 14, g32p_row04_traceSegment_085_1134_0013, g32p_row04_traceSegment_085_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1161 13 14, g32p_row04_traceSegment_085_1161_0013, g32p_row04_traceSegment_085_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1134 27 27, g32p_row04_traceSegment_085_1134_0027, g32p_row04_traceSegment_085_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1080 54 54, g32p_row04_traceSegment_085_1080_0054, g32p_row04_traceSegment_085_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1188 13 14, g32p_row04_traceSegment_085_1188_0013, g32p_row04_traceSegment_085_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1215 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1228 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1215 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1215 13 14, g32p_row04_traceSegment_085_1215_0013, g32p_row04_traceSegment_085_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1188 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1188 27 27, g32p_row04_traceSegment_085_1188_0027, g32p_row04_traceSegment_085_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1255 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1242 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1242 13 14, g32p_row04_traceSegment_085_1242_0013, g32p_row04_traceSegment_085_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1269 13 14, g32p_row04_traceSegment_085_1269_0013, g32p_row04_traceSegment_085_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1242 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1242 27 27, g32p_row04_traceSegment_085_1242_0027, g32p_row04_traceSegment_085_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 1188 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1188 54 54, g32p_row04_traceSegment_085_1188_0054, g32p_row04_traceSegment_085_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_085 1080 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1080 108 108, g32p_row04_traceSegment_085_1080_0108, g32p_row04_traceSegment_085_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_085 864 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 864 216 216, g32p_row04_traceSegment_085_0864_0216, g32p_row04_traceSegment_085_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1309 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1296 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1296 13 14, g32p_row04_traceSegment_085_1296_0013, g32p_row04_traceSegment_085_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1323 13 14, g32p_row04_traceSegment_085_1323_0013, g32p_row04_traceSegment_085_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1296 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1296 27 27, g32p_row04_traceSegment_085_1296_0027, g32p_row04_traceSegment_085_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1350 13 14, g32p_row04_traceSegment_085_1350_0013, g32p_row04_traceSegment_085_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1390 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1377 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1377 13 14, g32p_row04_traceSegment_085_1377_0013, g32p_row04_traceSegment_085_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1350 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1350 27 27, g32p_row04_traceSegment_085_1350_0027, g32p_row04_traceSegment_085_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 1296 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1296 54 54, g32p_row04_traceSegment_085_1296_0054, g32p_row04_traceSegment_085_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1404 13 14, g32p_row04_traceSegment_085_1404_0013, g32p_row04_traceSegment_085_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1431 13 14, g32p_row04_traceSegment_085_1431_0013, g32p_row04_traceSegment_085_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1404 27 27, g32p_row04_traceSegment_085_1404_0027, g32p_row04_traceSegment_085_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1458 13 14, g32p_row04_traceSegment_085_1458_0013, g32p_row04_traceSegment_085_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1485 13 14, g32p_row04_traceSegment_085_1485_0013, g32p_row04_traceSegment_085_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1458 27 27, g32p_row04_traceSegment_085_1458_0027, g32p_row04_traceSegment_085_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1404 54 54, g32p_row04_traceSegment_085_1404_0054, g32p_row04_traceSegment_085_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_085 1296 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1296 108 108, g32p_row04_traceSegment_085_1296_0108, g32p_row04_traceSegment_085_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1512 13 14, g32p_row04_traceSegment_085_1512_0013, g32p_row04_traceSegment_085_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1539 13 14, g32p_row04_traceSegment_085_1539_0013, g32p_row04_traceSegment_085_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1512 27 27, g32p_row04_traceSegment_085_1512_0027, g32p_row04_traceSegment_085_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1566 13 14, g32p_row04_traceSegment_085_1566_0013, g32p_row04_traceSegment_085_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1593 13 14, g32p_row04_traceSegment_085_1593_0013, g32p_row04_traceSegment_085_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1566 27 27, g32p_row04_traceSegment_085_1566_0027, g32p_row04_traceSegment_085_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1512 54 54, g32p_row04_traceSegment_085_1512_0054, g32p_row04_traceSegment_085_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1620 13 14, g32p_row04_traceSegment_085_1620_0013, g32p_row04_traceSegment_085_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1647 13 14, g32p_row04_traceSegment_085_1647_0013, g32p_row04_traceSegment_085_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1620 27 27, g32p_row04_traceSegment_085_1620_0027, g32p_row04_traceSegment_085_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1674 13 14, g32p_row04_traceSegment_085_1674_0013, g32p_row04_traceSegment_085_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_085 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_085 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_085_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_085 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1701 13 14, g32p_row04_traceSegment_085_1701_0013, g32p_row04_traceSegment_085_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_085 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1674 27 27, g32p_row04_traceSegment_085_1674_0027, g32p_row04_traceSegment_085_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_085 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1620 54 54, g32p_row04_traceSegment_085_1620_0054, g32p_row04_traceSegment_085_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_085 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1512 108 108, g32p_row04_traceSegment_085_1512_0108, g32p_row04_traceSegment_085_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_085_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_085 1296 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 1296 216 216, g32p_row04_traceSegment_085_1296_0216, g32p_row04_traceSegment_085_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_085 864 864 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 864 432 432, g32p_row04_traceSegment_085_0864_0432, g32p_row04_traceSegment_085_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_085_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_085 0 1728 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_085 0 864 864, g32p_row04_traceSegment_085_0000_0864, g32p_row04_traceSegment_085_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 85 = [0, 4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_085_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_086 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 86 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_086_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 0 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 0 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 0 13 14, g32p_row04_traceSegment_086_0000_0013, g32p_row04_traceSegment_086_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 27 13 14, g32p_row04_traceSegment_086_0027_0013, g32p_row04_traceSegment_086_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 0 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 0 27 27, g32p_row04_traceSegment_086_0000_0027, g32p_row04_traceSegment_086_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 54 13 14, g32p_row04_traceSegment_086_0054_0013, g32p_row04_traceSegment_086_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 94 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 81 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 81 13 14, g32p_row04_traceSegment_086_0081_0013, g32p_row04_traceSegment_086_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 54 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 54 27 27, g32p_row04_traceSegment_086_0054_0027, g32p_row04_traceSegment_086_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 0 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 0 54 54, g32p_row04_traceSegment_086_0000_0054, g32p_row04_traceSegment_086_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 108 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 108 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 108 13 14, g32p_row04_traceSegment_086_0108_0013, g32p_row04_traceSegment_086_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 135 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 135 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 135 13 14, g32p_row04_traceSegment_086_0135_0013, g32p_row04_traceSegment_086_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 108 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 108 27 27, g32p_row04_traceSegment_086_0108_0027, g32p_row04_traceSegment_086_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 162 13 14, g32p_row04_traceSegment_086_0162_0013, g32p_row04_traceSegment_086_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 189 13 14, g32p_row04_traceSegment_086_0189_0013, g32p_row04_traceSegment_086_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 162 27 27, g32p_row04_traceSegment_086_0162_0027, g32p_row04_traceSegment_086_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 108 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 108 54 54, g32p_row04_traceSegment_086_0108_0054, g32p_row04_traceSegment_086_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_086 0 216 = [7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 0 108 108, g32p_row04_traceSegment_086_0000_0108, g32p_row04_traceSegment_086_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 216 13 14, g32p_row04_traceSegment_086_0216_0013, g32p_row04_traceSegment_086_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 243 13 14, g32p_row04_traceSegment_086_0243_0013, g32p_row04_traceSegment_086_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 216 27 27, g32p_row04_traceSegment_086_0216_0027, g32p_row04_traceSegment_086_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 270 13 14, g32p_row04_traceSegment_086_0270_0013, g32p_row04_traceSegment_086_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 297 13 14, g32p_row04_traceSegment_086_0297_0013, g32p_row04_traceSegment_086_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 270 27 27, g32p_row04_traceSegment_086_0270_0027, g32p_row04_traceSegment_086_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 216 54 54, g32p_row04_traceSegment_086_0216_0054, g32p_row04_traceSegment_086_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 324 13 14, g32p_row04_traceSegment_086_0324_0013, g32p_row04_traceSegment_086_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 351 13 14, g32p_row04_traceSegment_086_0351_0013, g32p_row04_traceSegment_086_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 324 27 27, g32p_row04_traceSegment_086_0324_0027, g32p_row04_traceSegment_086_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 378 13 14, g32p_row04_traceSegment_086_0378_0013, g32p_row04_traceSegment_086_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 405 13 14, g32p_row04_traceSegment_086_0405_0013, g32p_row04_traceSegment_086_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 378 27 27, g32p_row04_traceSegment_086_0378_0027, g32p_row04_traceSegment_086_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 324 54 54, g32p_row04_traceSegment_086_0324_0054, g32p_row04_traceSegment_086_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_086 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 216 108 108, g32p_row04_traceSegment_086_0216_0108, g32p_row04_traceSegment_086_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_086 0 432 = [7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 0 216 216, g32p_row04_traceSegment_086_0000_0216, g32p_row04_traceSegment_086_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 432 13 14, g32p_row04_traceSegment_086_0432_0013, g32p_row04_traceSegment_086_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 459 13 14, g32p_row04_traceSegment_086_0459_0013, g32p_row04_traceSegment_086_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 432 27 27, g32p_row04_traceSegment_086_0432_0027, g32p_row04_traceSegment_086_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 486 13 14, g32p_row04_traceSegment_086_0486_0013, g32p_row04_traceSegment_086_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 526 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 513 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 513 13 14, g32p_row04_traceSegment_086_0513_0013, g32p_row04_traceSegment_086_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 486 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 486 27 27, g32p_row04_traceSegment_086_0486_0027, g32p_row04_traceSegment_086_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 432 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 432 54 54, g32p_row04_traceSegment_086_0432_0054, g32p_row04_traceSegment_086_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 553 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 540 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 540 13 14, g32p_row04_traceSegment_086_0540_0013, g32p_row04_traceSegment_086_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 567 13 14, g32p_row04_traceSegment_086_0567_0013, g32p_row04_traceSegment_086_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 540 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 540 27 27, g32p_row04_traceSegment_086_0540_0027, g32p_row04_traceSegment_086_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 607 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 594 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 594 13 14, g32p_row04_traceSegment_086_0594_0013, g32p_row04_traceSegment_086_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 621 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 634 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 621 27 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 621 13 14, g32p_row04_traceSegment_086_0621_0013, g32p_row04_traceSegment_086_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 594 54 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 594 27 27, g32p_row04_traceSegment_086_0594_0027, g32p_row04_traceSegment_086_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 540 108 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 540 54 54, g32p_row04_traceSegment_086_0540_0054, g32p_row04_traceSegment_086_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_086 432 216 = [3, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 432 108 108, g32p_row04_traceSegment_086_0432_0108, g32p_row04_traceSegment_086_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 648 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 648 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 648 13 14, g32p_row04_traceSegment_086_0648_0013, g32p_row04_traceSegment_086_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 675 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 688 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 675 27 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 675 13 14, g32p_row04_traceSegment_086_0675_0013, g32p_row04_traceSegment_086_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 648 54 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 648 27 27, g32p_row04_traceSegment_086_0648_0027, g32p_row04_traceSegment_086_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 702 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 715 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 702 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 702 13 14, g32p_row04_traceSegment_086_0702_0013, g32p_row04_traceSegment_086_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 742 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 729 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 729 13 14, g32p_row04_traceSegment_086_0729_0013, g32p_row04_traceSegment_086_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 702 54 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 702 27 27, g32p_row04_traceSegment_086_0702_0027, g32p_row04_traceSegment_086_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 648 108 = [1, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 648 54 54, g32p_row04_traceSegment_086_0648_0054, g32p_row04_traceSegment_086_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 769 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 756 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 756 13 14, g32p_row04_traceSegment_086_0756_0013, g32p_row04_traceSegment_086_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 783 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 796 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 783 27 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 783 13 14, g32p_row04_traceSegment_086_0783_0013, g32p_row04_traceSegment_086_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 756 54 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 756 27 27, g32p_row04_traceSegment_086_0756_0027, g32p_row04_traceSegment_086_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 810 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 823 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 810 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 810 13 14, g32p_row04_traceSegment_086_0810_0013, g32p_row04_traceSegment_086_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 837 13 14, g32p_row04_traceSegment_086_0837_0013, g32p_row04_traceSegment_086_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 810 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 810 27 27, g32p_row04_traceSegment_086_0810_0027, g32p_row04_traceSegment_086_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 756 108 = [2, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 756 54 54, g32p_row04_traceSegment_086_0756_0054, g32p_row04_traceSegment_086_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_086 648 216 = [3, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 648 108 108, g32p_row04_traceSegment_086_0648_0108, g32p_row04_traceSegment_086_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_086 432 432 = [6, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 432 216 216, g32p_row04_traceSegment_086_0432_0216, g32p_row04_traceSegment_086_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_086 0 864 = [13, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 0 432 432, g32p_row04_traceSegment_086_0000_0432, g32p_row04_traceSegment_086_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 864 13 14, g32p_row04_traceSegment_086_0864_0013, g32p_row04_traceSegment_086_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 891 13 14, g32p_row04_traceSegment_086_0891_0013, g32p_row04_traceSegment_086_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 864 27 27, g32p_row04_traceSegment_086_0864_0027, g32p_row04_traceSegment_086_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 918 13 14, g32p_row04_traceSegment_086_0918_0013, g32p_row04_traceSegment_086_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 945 13 14, g32p_row04_traceSegment_086_0945_0013, g32p_row04_traceSegment_086_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 918 27 27, g32p_row04_traceSegment_086_0918_0027, g32p_row04_traceSegment_086_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 864 54 54, g32p_row04_traceSegment_086_0864_0054, g32p_row04_traceSegment_086_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 972 13 14, g32p_row04_traceSegment_086_0972_0013, g32p_row04_traceSegment_086_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 999 13 14, g32p_row04_traceSegment_086_0999_0013, g32p_row04_traceSegment_086_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 972 27 27, g32p_row04_traceSegment_086_0972_0027, g32p_row04_traceSegment_086_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1026 13 14, g32p_row04_traceSegment_086_1026_0013, g32p_row04_traceSegment_086_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1053 13 14, g32p_row04_traceSegment_086_1053_0013, g32p_row04_traceSegment_086_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1026 27 27, g32p_row04_traceSegment_086_1026_0027, g32p_row04_traceSegment_086_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 972 54 54, g32p_row04_traceSegment_086_0972_0054, g32p_row04_traceSegment_086_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_086 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 864 108 108, g32p_row04_traceSegment_086_0864_0108, g32p_row04_traceSegment_086_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1080 13 14, g32p_row04_traceSegment_086_1080_0013, g32p_row04_traceSegment_086_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1107 13 14, g32p_row04_traceSegment_086_1107_0013, g32p_row04_traceSegment_086_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1080 27 27, g32p_row04_traceSegment_086_1080_0027, g32p_row04_traceSegment_086_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1134 13 14, g32p_row04_traceSegment_086_1134_0013, g32p_row04_traceSegment_086_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1161 13 14, g32p_row04_traceSegment_086_1161_0013, g32p_row04_traceSegment_086_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1134 27 27, g32p_row04_traceSegment_086_1134_0027, g32p_row04_traceSegment_086_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1080 54 54, g32p_row04_traceSegment_086_1080_0054, g32p_row04_traceSegment_086_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1188 13 14, g32p_row04_traceSegment_086_1188_0013, g32p_row04_traceSegment_086_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1215 13 14, g32p_row04_traceSegment_086_1215_0013, g32p_row04_traceSegment_086_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1188 27 27, g32p_row04_traceSegment_086_1188_0027, g32p_row04_traceSegment_086_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1242 13 14, g32p_row04_traceSegment_086_1242_0013, g32p_row04_traceSegment_086_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1269 13 14, g32p_row04_traceSegment_086_1269_0013, g32p_row04_traceSegment_086_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1242 27 27, g32p_row04_traceSegment_086_1242_0027, g32p_row04_traceSegment_086_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1188 54 54, g32p_row04_traceSegment_086_1188_0054, g32p_row04_traceSegment_086_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_086 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1080 108 108, g32p_row04_traceSegment_086_1080_0108, g32p_row04_traceSegment_086_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_086 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 864 216 216, g32p_row04_traceSegment_086_0864_0216, g32p_row04_traceSegment_086_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1296 13 14, g32p_row04_traceSegment_086_1296_0013, g32p_row04_traceSegment_086_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1323 13 14, g32p_row04_traceSegment_086_1323_0013, g32p_row04_traceSegment_086_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1296 27 27, g32p_row04_traceSegment_086_1296_0027, g32p_row04_traceSegment_086_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1350 13 14, g32p_row04_traceSegment_086_1350_0013, g32p_row04_traceSegment_086_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1377 13 14, g32p_row04_traceSegment_086_1377_0013, g32p_row04_traceSegment_086_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1350 27 27, g32p_row04_traceSegment_086_1350_0027, g32p_row04_traceSegment_086_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1296 54 54, g32p_row04_traceSegment_086_1296_0054, g32p_row04_traceSegment_086_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1404 13 14, g32p_row04_traceSegment_086_1404_0013, g32p_row04_traceSegment_086_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1431 13 14, g32p_row04_traceSegment_086_1431_0013, g32p_row04_traceSegment_086_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1404 27 27, g32p_row04_traceSegment_086_1404_0027, g32p_row04_traceSegment_086_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1458 13 14, g32p_row04_traceSegment_086_1458_0013, g32p_row04_traceSegment_086_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1485 13 14, g32p_row04_traceSegment_086_1485_0013, g32p_row04_traceSegment_086_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1458 27 27, g32p_row04_traceSegment_086_1458_0027, g32p_row04_traceSegment_086_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1404 54 54, g32p_row04_traceSegment_086_1404_0054, g32p_row04_traceSegment_086_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_086 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1296 108 108, g32p_row04_traceSegment_086_1296_0108, g32p_row04_traceSegment_086_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1525 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1512 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1512 13 14, g32p_row04_traceSegment_086_1512_0013, g32p_row04_traceSegment_086_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1539 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1539 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1539 13 14, g32p_row04_traceSegment_086_1539_0013, g32p_row04_traceSegment_086_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1512 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1512 27 27, g32p_row04_traceSegment_086_1512_0027, g32p_row04_traceSegment_086_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1566 13 14, g32p_row04_traceSegment_086_1566_0013, g32p_row04_traceSegment_086_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1593 13 14, g32p_row04_traceSegment_086_1593_0013, g32p_row04_traceSegment_086_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1566 27 27, g32p_row04_traceSegment_086_1566_0027, g32p_row04_traceSegment_086_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 1512 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1512 54 54, g32p_row04_traceSegment_086_1512_0054, g32p_row04_traceSegment_086_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1620 13 14, g32p_row04_traceSegment_086_1620_0013, g32p_row04_traceSegment_086_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1647 13 14, g32p_row04_traceSegment_086_1647_0013, g32p_row04_traceSegment_086_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1620 27 27, g32p_row04_traceSegment_086_1620_0027, g32p_row04_traceSegment_086_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1674 13 14, g32p_row04_traceSegment_086_1674_0013, g32p_row04_traceSegment_086_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_086 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_086 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_086_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_086 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1701 13 14, g32p_row04_traceSegment_086_1701_0013, g32p_row04_traceSegment_086_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_086 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1674 27 27, g32p_row04_traceSegment_086_1674_0027, g32p_row04_traceSegment_086_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_086 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1620 54 54, g32p_row04_traceSegment_086_1620_0054, g32p_row04_traceSegment_086_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_086 1512 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1512 108 108, g32p_row04_traceSegment_086_1512_0108, g32p_row04_traceSegment_086_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_086_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_086 1296 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 1296 216 216, g32p_row04_traceSegment_086_1296_0216, g32p_row04_traceSegment_086_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_086 864 864 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 864 432 432, g32p_row04_traceSegment_086_0864_0432, g32p_row04_traceSegment_086_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_086_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_086 0 1728 = [16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_086 0 864 864, g32p_row04_traceSegment_086_0000_0864, g32p_row04_traceSegment_086_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 86 = [16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_086_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_087 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 87 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_087_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 0 13 14, g32p_row04_traceSegment_087_0000_0013, g32p_row04_traceSegment_087_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 27 13 14, g32p_row04_traceSegment_087_0027_0013, g32p_row04_traceSegment_087_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 0 27 27, g32p_row04_traceSegment_087_0000_0027, g32p_row04_traceSegment_087_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 54 13 14, g32p_row04_traceSegment_087_0054_0013, g32p_row04_traceSegment_087_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 81 13 14, g32p_row04_traceSegment_087_0081_0013, g32p_row04_traceSegment_087_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 54 27 27, g32p_row04_traceSegment_087_0054_0027, g32p_row04_traceSegment_087_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 0 54 54, g32p_row04_traceSegment_087_0000_0054, g32p_row04_traceSegment_087_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 108 13 14, g32p_row04_traceSegment_087_0108_0013, g32p_row04_traceSegment_087_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 135 13 14, g32p_row04_traceSegment_087_0135_0013, g32p_row04_traceSegment_087_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 108 27 27, g32p_row04_traceSegment_087_0108_0027, g32p_row04_traceSegment_087_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 162 13 14, g32p_row04_traceSegment_087_0162_0013, g32p_row04_traceSegment_087_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 189 13 14, g32p_row04_traceSegment_087_0189_0013, g32p_row04_traceSegment_087_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 162 27 27, g32p_row04_traceSegment_087_0162_0027, g32p_row04_traceSegment_087_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 108 54 54, g32p_row04_traceSegment_087_0108_0054, g32p_row04_traceSegment_087_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_087 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 0 108 108, g32p_row04_traceSegment_087_0000_0108, g32p_row04_traceSegment_087_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 216 13 14, g32p_row04_traceSegment_087_0216_0013, g32p_row04_traceSegment_087_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 243 13 14, g32p_row04_traceSegment_087_0243_0013, g32p_row04_traceSegment_087_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 216 27 27, g32p_row04_traceSegment_087_0216_0027, g32p_row04_traceSegment_087_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 270 13 14, g32p_row04_traceSegment_087_0270_0013, g32p_row04_traceSegment_087_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 297 13 14, g32p_row04_traceSegment_087_0297_0013, g32p_row04_traceSegment_087_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 270 27 27, g32p_row04_traceSegment_087_0270_0027, g32p_row04_traceSegment_087_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 216 54 54, g32p_row04_traceSegment_087_0216_0054, g32p_row04_traceSegment_087_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 324 13 14, g32p_row04_traceSegment_087_0324_0013, g32p_row04_traceSegment_087_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 351 13 14, g32p_row04_traceSegment_087_0351_0013, g32p_row04_traceSegment_087_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 324 27 27, g32p_row04_traceSegment_087_0324_0027, g32p_row04_traceSegment_087_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 378 13 14, g32p_row04_traceSegment_087_0378_0013, g32p_row04_traceSegment_087_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 405 13 14, g32p_row04_traceSegment_087_0405_0013, g32p_row04_traceSegment_087_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 378 27 27, g32p_row04_traceSegment_087_0378_0027, g32p_row04_traceSegment_087_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 324 54 54, g32p_row04_traceSegment_087_0324_0054, g32p_row04_traceSegment_087_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_087 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 216 108 108, g32p_row04_traceSegment_087_0216_0108, g32p_row04_traceSegment_087_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_087 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 0 216 216, g32p_row04_traceSegment_087_0000_0216, g32p_row04_traceSegment_087_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 432 13 14, g32p_row04_traceSegment_087_0432_0013, g32p_row04_traceSegment_087_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 459 13 14, g32p_row04_traceSegment_087_0459_0013, g32p_row04_traceSegment_087_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 432 27 27, g32p_row04_traceSegment_087_0432_0027, g32p_row04_traceSegment_087_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 486 13 14, g32p_row04_traceSegment_087_0486_0013, g32p_row04_traceSegment_087_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 513 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 513 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 513 13 14, g32p_row04_traceSegment_087_0513_0013, g32p_row04_traceSegment_087_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 486 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 486 27 27, g32p_row04_traceSegment_087_0486_0027, g32p_row04_traceSegment_087_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 432 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 432 54 54, g32p_row04_traceSegment_087_0432_0054, g32p_row04_traceSegment_087_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 540 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 540 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 540 13 14, g32p_row04_traceSegment_087_0540_0013, g32p_row04_traceSegment_087_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 567 13 14, g32p_row04_traceSegment_087_0567_0013, g32p_row04_traceSegment_087_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 540 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 540 27 27, g32p_row04_traceSegment_087_0540_0027, g32p_row04_traceSegment_087_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 594 13 14, g32p_row04_traceSegment_087_0594_0013, g32p_row04_traceSegment_087_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 621 13 14, g32p_row04_traceSegment_087_0621_0013, g32p_row04_traceSegment_087_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 594 27 27, g32p_row04_traceSegment_087_0594_0027, g32p_row04_traceSegment_087_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 540 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 540 54 54, g32p_row04_traceSegment_087_0540_0054, g32p_row04_traceSegment_087_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_087 432 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 432 108 108, g32p_row04_traceSegment_087_0432_0108, g32p_row04_traceSegment_087_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 648 13 14, g32p_row04_traceSegment_087_0648_0013, g32p_row04_traceSegment_087_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 675 13 14, g32p_row04_traceSegment_087_0675_0013, g32p_row04_traceSegment_087_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 648 27 27, g32p_row04_traceSegment_087_0648_0027, g32p_row04_traceSegment_087_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 702 13 14, g32p_row04_traceSegment_087_0702_0013, g32p_row04_traceSegment_087_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 729 13 14, g32p_row04_traceSegment_087_0729_0013, g32p_row04_traceSegment_087_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 702 27 27, g32p_row04_traceSegment_087_0702_0027, g32p_row04_traceSegment_087_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 648 54 54, g32p_row04_traceSegment_087_0648_0054, g32p_row04_traceSegment_087_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 756 13 14, g32p_row04_traceSegment_087_0756_0013, g32p_row04_traceSegment_087_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 783 13 14, g32p_row04_traceSegment_087_0783_0013, g32p_row04_traceSegment_087_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 756 27 27, g32p_row04_traceSegment_087_0756_0027, g32p_row04_traceSegment_087_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 810 13 14, g32p_row04_traceSegment_087_0810_0013, g32p_row04_traceSegment_087_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 837 13 14, g32p_row04_traceSegment_087_0837_0013, g32p_row04_traceSegment_087_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 810 27 27, g32p_row04_traceSegment_087_0810_0027, g32p_row04_traceSegment_087_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 756 54 54, g32p_row04_traceSegment_087_0756_0054, g32p_row04_traceSegment_087_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_087 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 648 108 108, g32p_row04_traceSegment_087_0648_0108, g32p_row04_traceSegment_087_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_087 432 432 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 432 216 216, g32p_row04_traceSegment_087_0432_0216, g32p_row04_traceSegment_087_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_087 0 864 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 0 432 432, g32p_row04_traceSegment_087_0000_0432, g32p_row04_traceSegment_087_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 864 13 14, g32p_row04_traceSegment_087_0864_0013, g32p_row04_traceSegment_087_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 891 13 14, g32p_row04_traceSegment_087_0891_0013, g32p_row04_traceSegment_087_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 864 27 27, g32p_row04_traceSegment_087_0864_0027, g32p_row04_traceSegment_087_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 918 13 14, g32p_row04_traceSegment_087_0918_0013, g32p_row04_traceSegment_087_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 945 13 14, g32p_row04_traceSegment_087_0945_0013, g32p_row04_traceSegment_087_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 918 27 27, g32p_row04_traceSegment_087_0918_0027, g32p_row04_traceSegment_087_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 864 54 54, g32p_row04_traceSegment_087_0864_0054, g32p_row04_traceSegment_087_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 972 13 14, g32p_row04_traceSegment_087_0972_0013, g32p_row04_traceSegment_087_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 999 13 14, g32p_row04_traceSegment_087_0999_0013, g32p_row04_traceSegment_087_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 972 27 27, g32p_row04_traceSegment_087_0972_0027, g32p_row04_traceSegment_087_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1026 13 14, g32p_row04_traceSegment_087_1026_0013, g32p_row04_traceSegment_087_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1053 13 14, g32p_row04_traceSegment_087_1053_0013, g32p_row04_traceSegment_087_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1026 27 27, g32p_row04_traceSegment_087_1026_0027, g32p_row04_traceSegment_087_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 972 54 54, g32p_row04_traceSegment_087_0972_0054, g32p_row04_traceSegment_087_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_087 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 864 108 108, g32p_row04_traceSegment_087_0864_0108, g32p_row04_traceSegment_087_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1080 13 14, g32p_row04_traceSegment_087_1080_0013, g32p_row04_traceSegment_087_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1107 13 14, g32p_row04_traceSegment_087_1107_0013, g32p_row04_traceSegment_087_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1080 27 27, g32p_row04_traceSegment_087_1080_0027, g32p_row04_traceSegment_087_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1134 13 14, g32p_row04_traceSegment_087_1134_0013, g32p_row04_traceSegment_087_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1161 13 14, g32p_row04_traceSegment_087_1161_0013, g32p_row04_traceSegment_087_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1134 27 27, g32p_row04_traceSegment_087_1134_0027, g32p_row04_traceSegment_087_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1080 54 54, g32p_row04_traceSegment_087_1080_0054, g32p_row04_traceSegment_087_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1188 13 14, g32p_row04_traceSegment_087_1188_0013, g32p_row04_traceSegment_087_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1215 13 14, g32p_row04_traceSegment_087_1215_0013, g32p_row04_traceSegment_087_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1188 27 27, g32p_row04_traceSegment_087_1188_0027, g32p_row04_traceSegment_087_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1242 13 14, g32p_row04_traceSegment_087_1242_0013, g32p_row04_traceSegment_087_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1269 13 14, g32p_row04_traceSegment_087_1269_0013, g32p_row04_traceSegment_087_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1242 27 27, g32p_row04_traceSegment_087_1242_0027, g32p_row04_traceSegment_087_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1188 54 54, g32p_row04_traceSegment_087_1188_0054, g32p_row04_traceSegment_087_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_087 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1080 108 108, g32p_row04_traceSegment_087_1080_0108, g32p_row04_traceSegment_087_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_087 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 864 216 216, g32p_row04_traceSegment_087_0864_0216, g32p_row04_traceSegment_087_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1296 13 14, g32p_row04_traceSegment_087_1296_0013, g32p_row04_traceSegment_087_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1323 13 14, g32p_row04_traceSegment_087_1323_0013, g32p_row04_traceSegment_087_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1296 27 27, g32p_row04_traceSegment_087_1296_0027, g32p_row04_traceSegment_087_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1350 13 14, g32p_row04_traceSegment_087_1350_0013, g32p_row04_traceSegment_087_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1377 13 14, g32p_row04_traceSegment_087_1377_0013, g32p_row04_traceSegment_087_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1350 27 27, g32p_row04_traceSegment_087_1350_0027, g32p_row04_traceSegment_087_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1296 54 54, g32p_row04_traceSegment_087_1296_0054, g32p_row04_traceSegment_087_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1404 13 14, g32p_row04_traceSegment_087_1404_0013, g32p_row04_traceSegment_087_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1431 13 14, g32p_row04_traceSegment_087_1431_0013, g32p_row04_traceSegment_087_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1404 27 27, g32p_row04_traceSegment_087_1404_0027, g32p_row04_traceSegment_087_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1458 13 14, g32p_row04_traceSegment_087_1458_0013, g32p_row04_traceSegment_087_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1498 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1485 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1485 13 14, g32p_row04_traceSegment_087_1485_0013, g32p_row04_traceSegment_087_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1458 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1458 27 27, g32p_row04_traceSegment_087_1458_0027, g32p_row04_traceSegment_087_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 1404 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1404 54 54, g32p_row04_traceSegment_087_1404_0054, g32p_row04_traceSegment_087_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_087 1296 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1296 108 108, g32p_row04_traceSegment_087_1296_0108, g32p_row04_traceSegment_087_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1525 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1512 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1512 13 14, g32p_row04_traceSegment_087_1512_0013, g32p_row04_traceSegment_087_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1539 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1539 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1539 13 14, g32p_row04_traceSegment_087_1539_0013, g32p_row04_traceSegment_087_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1512 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1512 27 27, g32p_row04_traceSegment_087_1512_0027, g32p_row04_traceSegment_087_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1566 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1579 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1566 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1566 13 14, g32p_row04_traceSegment_087_1566_0013, g32p_row04_traceSegment_087_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1593 13 14, g32p_row04_traceSegment_087_1593_0013, g32p_row04_traceSegment_087_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1566 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1566 27 27, g32p_row04_traceSegment_087_1566_0027, g32p_row04_traceSegment_087_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 1512 108 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1512 54 54, g32p_row04_traceSegment_087_1512_0054, g32p_row04_traceSegment_087_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1620 13 14, g32p_row04_traceSegment_087_1620_0013, g32p_row04_traceSegment_087_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1647 13 14, g32p_row04_traceSegment_087_1647_0013, g32p_row04_traceSegment_087_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1620 27 27, g32p_row04_traceSegment_087_1620_0027, g32p_row04_traceSegment_087_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1674 13 14, g32p_row04_traceSegment_087_1674_0013, g32p_row04_traceSegment_087_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_087 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_087 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_087_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_087 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1701 13 14, g32p_row04_traceSegment_087_1701_0013, g32p_row04_traceSegment_087_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_087 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1674 27 27, g32p_row04_traceSegment_087_1674_0027, g32p_row04_traceSegment_087_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_087 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1620 54 54, g32p_row04_traceSegment_087_1620_0054, g32p_row04_traceSegment_087_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_087 1512 216 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1512 108 108, g32p_row04_traceSegment_087_1512_0108, g32p_row04_traceSegment_087_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_087_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_087 1296 432 = [0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 1296 216 216, g32p_row04_traceSegment_087_1296_0216, g32p_row04_traceSegment_087_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_087 864 864 = [0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 864 432 432, g32p_row04_traceSegment_087_0864_0432, g32p_row04_traceSegment_087_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_087_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_087 0 1728 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_087 0 864 864, g32p_row04_traceSegment_087_0000_0864, g32p_row04_traceSegment_087_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 87 = [0, 4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_087_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_tracePolynomial_080 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 80) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 80) (g32p_literalTraceValue 3 80)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_080]
  decide +kernel

theorem g32p_row04_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 81) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 81) (g32p_literalTraceValue 3 81)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_081]
  decide +kernel

theorem g32p_row04_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 82) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 82) (g32p_literalTraceValue 3 82)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_082]
  decide +kernel

theorem g32p_row04_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 83) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 83) (g32p_literalTraceValue 3 83)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_083]
  decide +kernel

theorem g32p_row04_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 84) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 84) (g32p_literalTraceValue 3 84)
      [1, 1, 1] [5184] = true := by
  rw [g32p_row04_traceCoefficients_084]
  decide +kernel

theorem g32p_row04_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 85) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 85) (g32p_literalTraceValue 3 85)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_085]
  decide +kernel

theorem g32p_row04_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 86) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 86) (g32p_literalTraceValue 3 86)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_086]
  decide +kernel

theorem g32p_row04_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 87) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 87) (g32p_literalTraceValue 3 87)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row04_traceCoefficients_087]
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

private def g32p_row04_traceSegment_088 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 88 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_088_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 0 13 14, g32p_row04_traceSegment_088_0000_0013, g32p_row04_traceSegment_088_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 27 13 14, g32p_row04_traceSegment_088_0027_0013, g32p_row04_traceSegment_088_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 0 27 27, g32p_row04_traceSegment_088_0000_0027, g32p_row04_traceSegment_088_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 67 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 54 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 54 13 14, g32p_row04_traceSegment_088_0054_0013, g32p_row04_traceSegment_088_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 81 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 81 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 81 13 14, g32p_row04_traceSegment_088_0081_0013, g32p_row04_traceSegment_088_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 54 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 54 27 27, g32p_row04_traceSegment_088_0054_0027, g32p_row04_traceSegment_088_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 0 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 0 54 54, g32p_row04_traceSegment_088_0000_0054, g32p_row04_traceSegment_088_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 108 13 14, g32p_row04_traceSegment_088_0108_0013, g32p_row04_traceSegment_088_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 135 13 14, g32p_row04_traceSegment_088_0135_0013, g32p_row04_traceSegment_088_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 108 27 27, g32p_row04_traceSegment_088_0108_0027, g32p_row04_traceSegment_088_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 162 13 14, g32p_row04_traceSegment_088_0162_0013, g32p_row04_traceSegment_088_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 189 13 14, g32p_row04_traceSegment_088_0189_0013, g32p_row04_traceSegment_088_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 162 27 27, g32p_row04_traceSegment_088_0162_0027, g32p_row04_traceSegment_088_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 108 54 54, g32p_row04_traceSegment_088_0108_0054, g32p_row04_traceSegment_088_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_088 0 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 0 108 108, g32p_row04_traceSegment_088_0000_0108, g32p_row04_traceSegment_088_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 216 13 14, g32p_row04_traceSegment_088_0216_0013, g32p_row04_traceSegment_088_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 243 13 14, g32p_row04_traceSegment_088_0243_0013, g32p_row04_traceSegment_088_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 216 27 27, g32p_row04_traceSegment_088_0216_0027, g32p_row04_traceSegment_088_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 270 13 14, g32p_row04_traceSegment_088_0270_0013, g32p_row04_traceSegment_088_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 297 13 14, g32p_row04_traceSegment_088_0297_0013, g32p_row04_traceSegment_088_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 270 27 27, g32p_row04_traceSegment_088_0270_0027, g32p_row04_traceSegment_088_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 216 54 54, g32p_row04_traceSegment_088_0216_0054, g32p_row04_traceSegment_088_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 324 13 14, g32p_row04_traceSegment_088_0324_0013, g32p_row04_traceSegment_088_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 351 13 14, g32p_row04_traceSegment_088_0351_0013, g32p_row04_traceSegment_088_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 324 27 27, g32p_row04_traceSegment_088_0324_0027, g32p_row04_traceSegment_088_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 378 13 14, g32p_row04_traceSegment_088_0378_0013, g32p_row04_traceSegment_088_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 405 13 14, g32p_row04_traceSegment_088_0405_0013, g32p_row04_traceSegment_088_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 378 27 27, g32p_row04_traceSegment_088_0378_0027, g32p_row04_traceSegment_088_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 324 54 54, g32p_row04_traceSegment_088_0324_0054, g32p_row04_traceSegment_088_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_088 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 216 108 108, g32p_row04_traceSegment_088_0216_0108, g32p_row04_traceSegment_088_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_088 0 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 0 216 216, g32p_row04_traceSegment_088_0000_0216, g32p_row04_traceSegment_088_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 432 13 14, g32p_row04_traceSegment_088_0432_0013, g32p_row04_traceSegment_088_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 459 13 14, g32p_row04_traceSegment_088_0459_0013, g32p_row04_traceSegment_088_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 432 27 27, g32p_row04_traceSegment_088_0432_0027, g32p_row04_traceSegment_088_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 486 13 14, g32p_row04_traceSegment_088_0486_0013, g32p_row04_traceSegment_088_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 526 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 513 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 513 13 14, g32p_row04_traceSegment_088_0513_0013, g32p_row04_traceSegment_088_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 486 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 486 27 27, g32p_row04_traceSegment_088_0486_0027, g32p_row04_traceSegment_088_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 432 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 432 54 54, g32p_row04_traceSegment_088_0432_0054, g32p_row04_traceSegment_088_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 540 13 14, g32p_row04_traceSegment_088_0540_0013, g32p_row04_traceSegment_088_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 567 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 567 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 567 13 14, g32p_row04_traceSegment_088_0567_0013, g32p_row04_traceSegment_088_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 540 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 540 27 27, g32p_row04_traceSegment_088_0540_0027, g32p_row04_traceSegment_088_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 594 13 14, g32p_row04_traceSegment_088_0594_0013, g32p_row04_traceSegment_088_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 621 13 14, g32p_row04_traceSegment_088_0621_0013, g32p_row04_traceSegment_088_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 594 27 27, g32p_row04_traceSegment_088_0594_0027, g32p_row04_traceSegment_088_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 540 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 540 54 54, g32p_row04_traceSegment_088_0540_0054, g32p_row04_traceSegment_088_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_088 432 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 432 108 108, g32p_row04_traceSegment_088_0432_0108, g32p_row04_traceSegment_088_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 648 13 14, g32p_row04_traceSegment_088_0648_0013, g32p_row04_traceSegment_088_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 675 13 14, g32p_row04_traceSegment_088_0675_0013, g32p_row04_traceSegment_088_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 648 27 27, g32p_row04_traceSegment_088_0648_0027, g32p_row04_traceSegment_088_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 702 13 14, g32p_row04_traceSegment_088_0702_0013, g32p_row04_traceSegment_088_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 729 13 14, g32p_row04_traceSegment_088_0729_0013, g32p_row04_traceSegment_088_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 702 27 27, g32p_row04_traceSegment_088_0702_0027, g32p_row04_traceSegment_088_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 648 54 54, g32p_row04_traceSegment_088_0648_0054, g32p_row04_traceSegment_088_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 756 13 14, g32p_row04_traceSegment_088_0756_0013, g32p_row04_traceSegment_088_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 783 13 14, g32p_row04_traceSegment_088_0783_0013, g32p_row04_traceSegment_088_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 756 27 27, g32p_row04_traceSegment_088_0756_0027, g32p_row04_traceSegment_088_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 810 13 14, g32p_row04_traceSegment_088_0810_0013, g32p_row04_traceSegment_088_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 837 13 14, g32p_row04_traceSegment_088_0837_0013, g32p_row04_traceSegment_088_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 810 27 27, g32p_row04_traceSegment_088_0810_0027, g32p_row04_traceSegment_088_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 756 54 54, g32p_row04_traceSegment_088_0756_0054, g32p_row04_traceSegment_088_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_088 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 648 108 108, g32p_row04_traceSegment_088_0648_0108, g32p_row04_traceSegment_088_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_088 432 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 432 216 216, g32p_row04_traceSegment_088_0432_0216, g32p_row04_traceSegment_088_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_088 0 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 0 432 432, g32p_row04_traceSegment_088_0000_0432, g32p_row04_traceSegment_088_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 864 13 14, g32p_row04_traceSegment_088_0864_0013, g32p_row04_traceSegment_088_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 891 13 14, g32p_row04_traceSegment_088_0891_0013, g32p_row04_traceSegment_088_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 864 27 27, g32p_row04_traceSegment_088_0864_0027, g32p_row04_traceSegment_088_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 918 13 14, g32p_row04_traceSegment_088_0918_0013, g32p_row04_traceSegment_088_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 945 13 14, g32p_row04_traceSegment_088_0945_0013, g32p_row04_traceSegment_088_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 918 27 27, g32p_row04_traceSegment_088_0918_0027, g32p_row04_traceSegment_088_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 864 54 54, g32p_row04_traceSegment_088_0864_0054, g32p_row04_traceSegment_088_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 972 13 14, g32p_row04_traceSegment_088_0972_0013, g32p_row04_traceSegment_088_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 999 13 14, g32p_row04_traceSegment_088_0999_0013, g32p_row04_traceSegment_088_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 972 27 27, g32p_row04_traceSegment_088_0972_0027, g32p_row04_traceSegment_088_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1026 13 14, g32p_row04_traceSegment_088_1026_0013, g32p_row04_traceSegment_088_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1053 13 14, g32p_row04_traceSegment_088_1053_0013, g32p_row04_traceSegment_088_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1026 27 27, g32p_row04_traceSegment_088_1026_0027, g32p_row04_traceSegment_088_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 972 54 54, g32p_row04_traceSegment_088_0972_0054, g32p_row04_traceSegment_088_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_088 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 864 108 108, g32p_row04_traceSegment_088_0864_0108, g32p_row04_traceSegment_088_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1080 13 14, g32p_row04_traceSegment_088_1080_0013, g32p_row04_traceSegment_088_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1107 13 14, g32p_row04_traceSegment_088_1107_0013, g32p_row04_traceSegment_088_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1080 27 27, g32p_row04_traceSegment_088_1080_0027, g32p_row04_traceSegment_088_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1134 13 14, g32p_row04_traceSegment_088_1134_0013, g32p_row04_traceSegment_088_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1161 13 14, g32p_row04_traceSegment_088_1161_0013, g32p_row04_traceSegment_088_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1134 27 27, g32p_row04_traceSegment_088_1134_0027, g32p_row04_traceSegment_088_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1080 54 54, g32p_row04_traceSegment_088_1080_0054, g32p_row04_traceSegment_088_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1188 13 14, g32p_row04_traceSegment_088_1188_0013, g32p_row04_traceSegment_088_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1215 13 14, g32p_row04_traceSegment_088_1215_0013, g32p_row04_traceSegment_088_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1188 27 27, g32p_row04_traceSegment_088_1188_0027, g32p_row04_traceSegment_088_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1242 13 14, g32p_row04_traceSegment_088_1242_0013, g32p_row04_traceSegment_088_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1269 13 14, g32p_row04_traceSegment_088_1269_0013, g32p_row04_traceSegment_088_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1242 27 27, g32p_row04_traceSegment_088_1242_0027, g32p_row04_traceSegment_088_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1188 54 54, g32p_row04_traceSegment_088_1188_0054, g32p_row04_traceSegment_088_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_088 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1080 108 108, g32p_row04_traceSegment_088_1080_0108, g32p_row04_traceSegment_088_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_088 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 864 216 216, g32p_row04_traceSegment_088_0864_0216, g32p_row04_traceSegment_088_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1296 13 14, g32p_row04_traceSegment_088_1296_0013, g32p_row04_traceSegment_088_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1323 13 14, g32p_row04_traceSegment_088_1323_0013, g32p_row04_traceSegment_088_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1296 27 27, g32p_row04_traceSegment_088_1296_0027, g32p_row04_traceSegment_088_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1350 13 14, g32p_row04_traceSegment_088_1350_0013, g32p_row04_traceSegment_088_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1377 13 14, g32p_row04_traceSegment_088_1377_0013, g32p_row04_traceSegment_088_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1350 27 27, g32p_row04_traceSegment_088_1350_0027, g32p_row04_traceSegment_088_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1296 54 54, g32p_row04_traceSegment_088_1296_0054, g32p_row04_traceSegment_088_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1404 13 14, g32p_row04_traceSegment_088_1404_0013, g32p_row04_traceSegment_088_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1431 13 14, g32p_row04_traceSegment_088_1431_0013, g32p_row04_traceSegment_088_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1404 27 27, g32p_row04_traceSegment_088_1404_0027, g32p_row04_traceSegment_088_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1458 13 14, g32p_row04_traceSegment_088_1458_0013, g32p_row04_traceSegment_088_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1485 13 14, g32p_row04_traceSegment_088_1485_0013, g32p_row04_traceSegment_088_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1458 27 27, g32p_row04_traceSegment_088_1458_0027, g32p_row04_traceSegment_088_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1404 54 54, g32p_row04_traceSegment_088_1404_0054, g32p_row04_traceSegment_088_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_088 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1296 108 108, g32p_row04_traceSegment_088_1296_0108, g32p_row04_traceSegment_088_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1512 13 14, g32p_row04_traceSegment_088_1512_0013, g32p_row04_traceSegment_088_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1539 13 14, g32p_row04_traceSegment_088_1539_0013, g32p_row04_traceSegment_088_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1512 27 27, g32p_row04_traceSegment_088_1512_0027, g32p_row04_traceSegment_088_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1566 13 14, g32p_row04_traceSegment_088_1566_0013, g32p_row04_traceSegment_088_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1593 13 14, g32p_row04_traceSegment_088_1593_0013, g32p_row04_traceSegment_088_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1566 27 27, g32p_row04_traceSegment_088_1566_0027, g32p_row04_traceSegment_088_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1512 54 54, g32p_row04_traceSegment_088_1512_0054, g32p_row04_traceSegment_088_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1620 13 14, g32p_row04_traceSegment_088_1620_0013, g32p_row04_traceSegment_088_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1647 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1660 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1647 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1647 13 14, g32p_row04_traceSegment_088_1647_0013, g32p_row04_traceSegment_088_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1620 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1620 27 27, g32p_row04_traceSegment_088_1620_0027, g32p_row04_traceSegment_088_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1674 13 14, g32p_row04_traceSegment_088_1674_0013, g32p_row04_traceSegment_088_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_088 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_088 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_088_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_088 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1701 13 14, g32p_row04_traceSegment_088_1701_0013, g32p_row04_traceSegment_088_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_088 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1674 27 27, g32p_row04_traceSegment_088_1674_0027, g32p_row04_traceSegment_088_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_088 1620 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1620 54 54, g32p_row04_traceSegment_088_1620_0054, g32p_row04_traceSegment_088_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_088 1512 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1512 108 108, g32p_row04_traceSegment_088_1512_0108, g32p_row04_traceSegment_088_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_088_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_088 1296 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 1296 216 216, g32p_row04_traceSegment_088_1296_0216, g32p_row04_traceSegment_088_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_088 864 864 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 864 432 432, g32p_row04_traceSegment_088_0864_0432, g32p_row04_traceSegment_088_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_088_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_088 0 1728 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_088 0 864 864, g32p_row04_traceSegment_088_0000_0864, g32p_row04_traceSegment_088_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 88 = [0, 4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_088_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_089 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 89 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_089_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 0 13 14, g32p_row04_traceSegment_089_0000_0013, g32p_row04_traceSegment_089_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 27 13 14, g32p_row04_traceSegment_089_0027_0013, g32p_row04_traceSegment_089_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 0 27 27, g32p_row04_traceSegment_089_0000_0027, g32p_row04_traceSegment_089_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 54 13 14, g32p_row04_traceSegment_089_0054_0013, g32p_row04_traceSegment_089_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 81 13 14, g32p_row04_traceSegment_089_0081_0013, g32p_row04_traceSegment_089_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 54 27 27, g32p_row04_traceSegment_089_0054_0027, g32p_row04_traceSegment_089_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 0 54 54, g32p_row04_traceSegment_089_0000_0054, g32p_row04_traceSegment_089_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 108 13 14, g32p_row04_traceSegment_089_0108_0013, g32p_row04_traceSegment_089_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 135 13 14, g32p_row04_traceSegment_089_0135_0013, g32p_row04_traceSegment_089_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 108 27 27, g32p_row04_traceSegment_089_0108_0027, g32p_row04_traceSegment_089_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 162 13 14, g32p_row04_traceSegment_089_0162_0013, g32p_row04_traceSegment_089_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 189 13 14, g32p_row04_traceSegment_089_0189_0013, g32p_row04_traceSegment_089_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 162 27 27, g32p_row04_traceSegment_089_0162_0027, g32p_row04_traceSegment_089_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 108 54 54, g32p_row04_traceSegment_089_0108_0054, g32p_row04_traceSegment_089_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_089 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 0 108 108, g32p_row04_traceSegment_089_0000_0108, g32p_row04_traceSegment_089_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 216 13 14, g32p_row04_traceSegment_089_0216_0013, g32p_row04_traceSegment_089_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 243 13 14, g32p_row04_traceSegment_089_0243_0013, g32p_row04_traceSegment_089_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 216 27 27, g32p_row04_traceSegment_089_0216_0027, g32p_row04_traceSegment_089_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 270 13 14, g32p_row04_traceSegment_089_0270_0013, g32p_row04_traceSegment_089_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 297 13 14, g32p_row04_traceSegment_089_0297_0013, g32p_row04_traceSegment_089_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 270 27 27, g32p_row04_traceSegment_089_0270_0027, g32p_row04_traceSegment_089_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 216 54 54, g32p_row04_traceSegment_089_0216_0054, g32p_row04_traceSegment_089_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 324 13 14, g32p_row04_traceSegment_089_0324_0013, g32p_row04_traceSegment_089_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 351 13 14, g32p_row04_traceSegment_089_0351_0013, g32p_row04_traceSegment_089_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 324 27 27, g32p_row04_traceSegment_089_0324_0027, g32p_row04_traceSegment_089_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 378 13 14, g32p_row04_traceSegment_089_0378_0013, g32p_row04_traceSegment_089_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 405 13 14, g32p_row04_traceSegment_089_0405_0013, g32p_row04_traceSegment_089_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 378 27 27, g32p_row04_traceSegment_089_0378_0027, g32p_row04_traceSegment_089_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 324 54 54, g32p_row04_traceSegment_089_0324_0054, g32p_row04_traceSegment_089_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_089 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 216 108 108, g32p_row04_traceSegment_089_0216_0108, g32p_row04_traceSegment_089_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_089 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 0 216 216, g32p_row04_traceSegment_089_0000_0216, g32p_row04_traceSegment_089_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 432 13 14, g32p_row04_traceSegment_089_0432_0013, g32p_row04_traceSegment_089_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 459 13 14, g32p_row04_traceSegment_089_0459_0013, g32p_row04_traceSegment_089_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 432 27 27, g32p_row04_traceSegment_089_0432_0027, g32p_row04_traceSegment_089_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 486 13 14, g32p_row04_traceSegment_089_0486_0013, g32p_row04_traceSegment_089_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 513 13 14, g32p_row04_traceSegment_089_0513_0013, g32p_row04_traceSegment_089_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 486 27 27, g32p_row04_traceSegment_089_0486_0027, g32p_row04_traceSegment_089_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 432 54 54, g32p_row04_traceSegment_089_0432_0054, g32p_row04_traceSegment_089_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 540 13 14, g32p_row04_traceSegment_089_0540_0013, g32p_row04_traceSegment_089_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 567 13 14, g32p_row04_traceSegment_089_0567_0013, g32p_row04_traceSegment_089_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 540 27 27, g32p_row04_traceSegment_089_0540_0027, g32p_row04_traceSegment_089_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 594 13 14, g32p_row04_traceSegment_089_0594_0013, g32p_row04_traceSegment_089_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 621 13 14, g32p_row04_traceSegment_089_0621_0013, g32p_row04_traceSegment_089_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 594 27 27, g32p_row04_traceSegment_089_0594_0027, g32p_row04_traceSegment_089_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 540 54 54, g32p_row04_traceSegment_089_0540_0054, g32p_row04_traceSegment_089_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_089 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 432 108 108, g32p_row04_traceSegment_089_0432_0108, g32p_row04_traceSegment_089_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 648 13 14, g32p_row04_traceSegment_089_0648_0013, g32p_row04_traceSegment_089_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 675 13 14, g32p_row04_traceSegment_089_0675_0013, g32p_row04_traceSegment_089_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 648 27 27, g32p_row04_traceSegment_089_0648_0027, g32p_row04_traceSegment_089_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 702 13 14, g32p_row04_traceSegment_089_0702_0013, g32p_row04_traceSegment_089_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 729 13 14, g32p_row04_traceSegment_089_0729_0013, g32p_row04_traceSegment_089_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 702 27 27, g32p_row04_traceSegment_089_0702_0027, g32p_row04_traceSegment_089_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 648 54 54, g32p_row04_traceSegment_089_0648_0054, g32p_row04_traceSegment_089_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 756 13 14, g32p_row04_traceSegment_089_0756_0013, g32p_row04_traceSegment_089_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 783 13 14, g32p_row04_traceSegment_089_0783_0013, g32p_row04_traceSegment_089_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 756 27 27, g32p_row04_traceSegment_089_0756_0027, g32p_row04_traceSegment_089_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 810 13 14, g32p_row04_traceSegment_089_0810_0013, g32p_row04_traceSegment_089_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 837 13 14, g32p_row04_traceSegment_089_0837_0013, g32p_row04_traceSegment_089_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 810 27 27, g32p_row04_traceSegment_089_0810_0027, g32p_row04_traceSegment_089_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 756 54 54, g32p_row04_traceSegment_089_0756_0054, g32p_row04_traceSegment_089_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_089 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 648 108 108, g32p_row04_traceSegment_089_0648_0108, g32p_row04_traceSegment_089_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_089 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 432 216 216, g32p_row04_traceSegment_089_0432_0216, g32p_row04_traceSegment_089_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_089 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 0 432 432, g32p_row04_traceSegment_089_0000_0432, g32p_row04_traceSegment_089_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 864 13 14, g32p_row04_traceSegment_089_0864_0013, g32p_row04_traceSegment_089_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 891 13 14, g32p_row04_traceSegment_089_0891_0013, g32p_row04_traceSegment_089_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 864 27 27, g32p_row04_traceSegment_089_0864_0027, g32p_row04_traceSegment_089_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 918 13 14, g32p_row04_traceSegment_089_0918_0013, g32p_row04_traceSegment_089_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 945 13 14, g32p_row04_traceSegment_089_0945_0013, g32p_row04_traceSegment_089_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 918 27 27, g32p_row04_traceSegment_089_0918_0027, g32p_row04_traceSegment_089_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 864 54 54, g32p_row04_traceSegment_089_0864_0054, g32p_row04_traceSegment_089_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 972 13 14, g32p_row04_traceSegment_089_0972_0013, g32p_row04_traceSegment_089_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 999 13 14, g32p_row04_traceSegment_089_0999_0013, g32p_row04_traceSegment_089_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 972 27 27, g32p_row04_traceSegment_089_0972_0027, g32p_row04_traceSegment_089_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1039 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1026 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1026 13 14, g32p_row04_traceSegment_089_1026_0013, g32p_row04_traceSegment_089_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1066 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1053 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1053 13 14, g32p_row04_traceSegment_089_1053_0013, g32p_row04_traceSegment_089_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1026 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1026 27 27, g32p_row04_traceSegment_089_1026_0027, g32p_row04_traceSegment_089_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 972 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 972 54 54, g32p_row04_traceSegment_089_0972_0054, g32p_row04_traceSegment_089_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_089 864 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 864 108 108, g32p_row04_traceSegment_089_0864_0108, g32p_row04_traceSegment_089_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1080 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1080 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1080 13 14, g32p_row04_traceSegment_089_1080_0013, g32p_row04_traceSegment_089_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1120 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1107 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1107 13 14, g32p_row04_traceSegment_089_1107_0013, g32p_row04_traceSegment_089_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1080 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1080 27 27, g32p_row04_traceSegment_089_1080_0027, g32p_row04_traceSegment_089_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1134 13 14, g32p_row04_traceSegment_089_1134_0013, g32p_row04_traceSegment_089_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1161 13 14, g32p_row04_traceSegment_089_1161_0013, g32p_row04_traceSegment_089_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1134 27 27, g32p_row04_traceSegment_089_1134_0027, g32p_row04_traceSegment_089_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 1080 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1080 54 54, g32p_row04_traceSegment_089_1080_0054, g32p_row04_traceSegment_089_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1188 13 14, g32p_row04_traceSegment_089_1188_0013, g32p_row04_traceSegment_089_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1215 13 14, g32p_row04_traceSegment_089_1215_0013, g32p_row04_traceSegment_089_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1188 27 27, g32p_row04_traceSegment_089_1188_0027, g32p_row04_traceSegment_089_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1242 13 14, g32p_row04_traceSegment_089_1242_0013, g32p_row04_traceSegment_089_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1269 13 14, g32p_row04_traceSegment_089_1269_0013, g32p_row04_traceSegment_089_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1242 27 27, g32p_row04_traceSegment_089_1242_0027, g32p_row04_traceSegment_089_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1188 54 54, g32p_row04_traceSegment_089_1188_0054, g32p_row04_traceSegment_089_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_089 1080 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1080 108 108, g32p_row04_traceSegment_089_1080_0108, g32p_row04_traceSegment_089_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_089 864 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 864 216 216, g32p_row04_traceSegment_089_0864_0216, g32p_row04_traceSegment_089_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1296 13 14, g32p_row04_traceSegment_089_1296_0013, g32p_row04_traceSegment_089_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1323 13 14, g32p_row04_traceSegment_089_1323_0013, g32p_row04_traceSegment_089_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1296 27 27, g32p_row04_traceSegment_089_1296_0027, g32p_row04_traceSegment_089_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1350 13 14, g32p_row04_traceSegment_089_1350_0013, g32p_row04_traceSegment_089_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1377 13 14, g32p_row04_traceSegment_089_1377_0013, g32p_row04_traceSegment_089_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1350 27 27, g32p_row04_traceSegment_089_1350_0027, g32p_row04_traceSegment_089_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1296 54 54, g32p_row04_traceSegment_089_1296_0054, g32p_row04_traceSegment_089_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1404 13 14, g32p_row04_traceSegment_089_1404_0013, g32p_row04_traceSegment_089_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1431 13 14, g32p_row04_traceSegment_089_1431_0013, g32p_row04_traceSegment_089_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1404 27 27, g32p_row04_traceSegment_089_1404_0027, g32p_row04_traceSegment_089_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1458 13 14, g32p_row04_traceSegment_089_1458_0013, g32p_row04_traceSegment_089_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1485 13 14, g32p_row04_traceSegment_089_1485_0013, g32p_row04_traceSegment_089_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1458 27 27, g32p_row04_traceSegment_089_1458_0027, g32p_row04_traceSegment_089_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1404 54 54, g32p_row04_traceSegment_089_1404_0054, g32p_row04_traceSegment_089_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_089 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1296 108 108, g32p_row04_traceSegment_089_1296_0108, g32p_row04_traceSegment_089_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1512 13 14, g32p_row04_traceSegment_089_1512_0013, g32p_row04_traceSegment_089_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1539 13 14, g32p_row04_traceSegment_089_1539_0013, g32p_row04_traceSegment_089_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1512 27 27, g32p_row04_traceSegment_089_1512_0027, g32p_row04_traceSegment_089_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1566 13 14, g32p_row04_traceSegment_089_1566_0013, g32p_row04_traceSegment_089_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1593 13 14, g32p_row04_traceSegment_089_1593_0013, g32p_row04_traceSegment_089_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1566 27 27, g32p_row04_traceSegment_089_1566_0027, g32p_row04_traceSegment_089_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1512 54 54, g32p_row04_traceSegment_089_1512_0054, g32p_row04_traceSegment_089_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1620 13 14, g32p_row04_traceSegment_089_1620_0013, g32p_row04_traceSegment_089_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1647 13 14, g32p_row04_traceSegment_089_1647_0013, g32p_row04_traceSegment_089_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1620 27 27, g32p_row04_traceSegment_089_1620_0027, g32p_row04_traceSegment_089_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1687 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1674 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1674 13 14, g32p_row04_traceSegment_089_1674_0013, g32p_row04_traceSegment_089_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_089 1701 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_089 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_089_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_089 1701 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1701 13 14, g32p_row04_traceSegment_089_1701_0013, g32p_row04_traceSegment_089_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_089 1674 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1674 27 27, g32p_row04_traceSegment_089_1674_0027, g32p_row04_traceSegment_089_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_089 1620 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1620 54 54, g32p_row04_traceSegment_089_1620_0054, g32p_row04_traceSegment_089_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_089 1512 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1512 108 108, g32p_row04_traceSegment_089_1512_0108, g32p_row04_traceSegment_089_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_089_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_089 1296 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 1296 216 216, g32p_row04_traceSegment_089_1296_0216, g32p_row04_traceSegment_089_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_089 864 864 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 864 432 432, g32p_row04_traceSegment_089_0864_0432, g32p_row04_traceSegment_089_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_089_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_089 0 1728 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_089 0 864 864, g32p_row04_traceSegment_089_0000_0864, g32p_row04_traceSegment_089_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 89 = [4, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_089_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_090 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 90 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_090_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 0 13 14, g32p_row04_traceSegment_090_0000_0013, g32p_row04_traceSegment_090_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 27 13 14, g32p_row04_traceSegment_090_0027_0013, g32p_row04_traceSegment_090_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 0 27 27, g32p_row04_traceSegment_090_0000_0027, g32p_row04_traceSegment_090_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 54 13 14, g32p_row04_traceSegment_090_0054_0013, g32p_row04_traceSegment_090_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 81 13 14, g32p_row04_traceSegment_090_0081_0013, g32p_row04_traceSegment_090_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 54 27 27, g32p_row04_traceSegment_090_0054_0027, g32p_row04_traceSegment_090_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 0 54 54, g32p_row04_traceSegment_090_0000_0054, g32p_row04_traceSegment_090_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 108 13 14, g32p_row04_traceSegment_090_0108_0013, g32p_row04_traceSegment_090_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 135 13 14, g32p_row04_traceSegment_090_0135_0013, g32p_row04_traceSegment_090_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 108 27 27, g32p_row04_traceSegment_090_0108_0027, g32p_row04_traceSegment_090_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 162 13 14, g32p_row04_traceSegment_090_0162_0013, g32p_row04_traceSegment_090_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 189 13 14, g32p_row04_traceSegment_090_0189_0013, g32p_row04_traceSegment_090_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 162 27 27, g32p_row04_traceSegment_090_0162_0027, g32p_row04_traceSegment_090_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 108 54 54, g32p_row04_traceSegment_090_0108_0054, g32p_row04_traceSegment_090_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_090 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 0 108 108, g32p_row04_traceSegment_090_0000_0108, g32p_row04_traceSegment_090_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 216 13 14, g32p_row04_traceSegment_090_0216_0013, g32p_row04_traceSegment_090_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 243 13 14, g32p_row04_traceSegment_090_0243_0013, g32p_row04_traceSegment_090_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 216 27 27, g32p_row04_traceSegment_090_0216_0027, g32p_row04_traceSegment_090_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 270 13 14, g32p_row04_traceSegment_090_0270_0013, g32p_row04_traceSegment_090_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 297 13 14, g32p_row04_traceSegment_090_0297_0013, g32p_row04_traceSegment_090_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 270 27 27, g32p_row04_traceSegment_090_0270_0027, g32p_row04_traceSegment_090_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 216 54 54, g32p_row04_traceSegment_090_0216_0054, g32p_row04_traceSegment_090_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 324 13 14, g32p_row04_traceSegment_090_0324_0013, g32p_row04_traceSegment_090_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 351 13 14, g32p_row04_traceSegment_090_0351_0013, g32p_row04_traceSegment_090_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 324 27 27, g32p_row04_traceSegment_090_0324_0027, g32p_row04_traceSegment_090_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 378 13 14, g32p_row04_traceSegment_090_0378_0013, g32p_row04_traceSegment_090_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 405 13 14, g32p_row04_traceSegment_090_0405_0013, g32p_row04_traceSegment_090_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 378 27 27, g32p_row04_traceSegment_090_0378_0027, g32p_row04_traceSegment_090_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 324 54 54, g32p_row04_traceSegment_090_0324_0054, g32p_row04_traceSegment_090_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_090 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 216 108 108, g32p_row04_traceSegment_090_0216_0108, g32p_row04_traceSegment_090_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_090 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 0 216 216, g32p_row04_traceSegment_090_0000_0216, g32p_row04_traceSegment_090_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 432 13 14, g32p_row04_traceSegment_090_0432_0013, g32p_row04_traceSegment_090_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 459 13 14, g32p_row04_traceSegment_090_0459_0013, g32p_row04_traceSegment_090_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 432 27 27, g32p_row04_traceSegment_090_0432_0027, g32p_row04_traceSegment_090_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 486 13 14, g32p_row04_traceSegment_090_0486_0013, g32p_row04_traceSegment_090_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 513 13 14, g32p_row04_traceSegment_090_0513_0013, g32p_row04_traceSegment_090_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 486 27 27, g32p_row04_traceSegment_090_0486_0027, g32p_row04_traceSegment_090_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 432 54 54, g32p_row04_traceSegment_090_0432_0054, g32p_row04_traceSegment_090_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 540 13 14, g32p_row04_traceSegment_090_0540_0013, g32p_row04_traceSegment_090_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 567 13 14, g32p_row04_traceSegment_090_0567_0013, g32p_row04_traceSegment_090_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 540 27 27, g32p_row04_traceSegment_090_0540_0027, g32p_row04_traceSegment_090_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 594 13 14, g32p_row04_traceSegment_090_0594_0013, g32p_row04_traceSegment_090_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 621 13 14, g32p_row04_traceSegment_090_0621_0013, g32p_row04_traceSegment_090_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 594 27 27, g32p_row04_traceSegment_090_0594_0027, g32p_row04_traceSegment_090_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 540 54 54, g32p_row04_traceSegment_090_0540_0054, g32p_row04_traceSegment_090_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_090 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 432 108 108, g32p_row04_traceSegment_090_0432_0108, g32p_row04_traceSegment_090_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 648 13 14, g32p_row04_traceSegment_090_0648_0013, g32p_row04_traceSegment_090_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 675 13 14, g32p_row04_traceSegment_090_0675_0013, g32p_row04_traceSegment_090_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 648 27 27, g32p_row04_traceSegment_090_0648_0027, g32p_row04_traceSegment_090_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 702 13 14, g32p_row04_traceSegment_090_0702_0013, g32p_row04_traceSegment_090_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 729 13 14, g32p_row04_traceSegment_090_0729_0013, g32p_row04_traceSegment_090_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 702 27 27, g32p_row04_traceSegment_090_0702_0027, g32p_row04_traceSegment_090_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 648 54 54, g32p_row04_traceSegment_090_0648_0054, g32p_row04_traceSegment_090_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 756 13 14, g32p_row04_traceSegment_090_0756_0013, g32p_row04_traceSegment_090_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 783 13 14, g32p_row04_traceSegment_090_0783_0013, g32p_row04_traceSegment_090_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 756 27 27, g32p_row04_traceSegment_090_0756_0027, g32p_row04_traceSegment_090_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 810 13 14, g32p_row04_traceSegment_090_0810_0013, g32p_row04_traceSegment_090_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 837 13 14, g32p_row04_traceSegment_090_0837_0013, g32p_row04_traceSegment_090_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 810 27 27, g32p_row04_traceSegment_090_0810_0027, g32p_row04_traceSegment_090_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 756 54 54, g32p_row04_traceSegment_090_0756_0054, g32p_row04_traceSegment_090_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_090 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 648 108 108, g32p_row04_traceSegment_090_0648_0108, g32p_row04_traceSegment_090_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_090 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 432 216 216, g32p_row04_traceSegment_090_0432_0216, g32p_row04_traceSegment_090_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_090 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 0 432 432, g32p_row04_traceSegment_090_0000_0432, g32p_row04_traceSegment_090_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 864 13 14, g32p_row04_traceSegment_090_0864_0013, g32p_row04_traceSegment_090_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 891 13 14, g32p_row04_traceSegment_090_0891_0013, g32p_row04_traceSegment_090_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 864 27 27, g32p_row04_traceSegment_090_0864_0027, g32p_row04_traceSegment_090_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 918 13 14, g32p_row04_traceSegment_090_0918_0013, g32p_row04_traceSegment_090_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 945 13 14, g32p_row04_traceSegment_090_0945_0013, g32p_row04_traceSegment_090_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 918 27 27, g32p_row04_traceSegment_090_0918_0027, g32p_row04_traceSegment_090_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 864 54 54, g32p_row04_traceSegment_090_0864_0054, g32p_row04_traceSegment_090_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 972 13 14, g32p_row04_traceSegment_090_0972_0013, g32p_row04_traceSegment_090_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 999 13 14, g32p_row04_traceSegment_090_0999_0013, g32p_row04_traceSegment_090_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 972 27 27, g32p_row04_traceSegment_090_0972_0027, g32p_row04_traceSegment_090_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1026 13 14, g32p_row04_traceSegment_090_1026_0013, g32p_row04_traceSegment_090_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1053 13 14, g32p_row04_traceSegment_090_1053_0013, g32p_row04_traceSegment_090_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1026 27 27, g32p_row04_traceSegment_090_1026_0027, g32p_row04_traceSegment_090_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 972 54 54, g32p_row04_traceSegment_090_0972_0054, g32p_row04_traceSegment_090_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_090 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 864 108 108, g32p_row04_traceSegment_090_0864_0108, g32p_row04_traceSegment_090_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1080 13 14, g32p_row04_traceSegment_090_1080_0013, g32p_row04_traceSegment_090_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1107 13 14, g32p_row04_traceSegment_090_1107_0013, g32p_row04_traceSegment_090_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1080 27 27, g32p_row04_traceSegment_090_1080_0027, g32p_row04_traceSegment_090_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1134 13 14, g32p_row04_traceSegment_090_1134_0013, g32p_row04_traceSegment_090_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1161 13 14, g32p_row04_traceSegment_090_1161_0013, g32p_row04_traceSegment_090_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1134 27 27, g32p_row04_traceSegment_090_1134_0027, g32p_row04_traceSegment_090_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1080 54 54, g32p_row04_traceSegment_090_1080_0054, g32p_row04_traceSegment_090_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1188 13 14, g32p_row04_traceSegment_090_1188_0013, g32p_row04_traceSegment_090_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1215 13 14, g32p_row04_traceSegment_090_1215_0013, g32p_row04_traceSegment_090_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1188 27 27, g32p_row04_traceSegment_090_1188_0027, g32p_row04_traceSegment_090_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1242 13 14, g32p_row04_traceSegment_090_1242_0013, g32p_row04_traceSegment_090_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1282 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1269 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1269 13 14, g32p_row04_traceSegment_090_1269_0013, g32p_row04_traceSegment_090_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1242 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1242 27 27, g32p_row04_traceSegment_090_1242_0027, g32p_row04_traceSegment_090_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 1188 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1188 54 54, g32p_row04_traceSegment_090_1188_0054, g32p_row04_traceSegment_090_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_090 1080 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1080 108 108, g32p_row04_traceSegment_090_1080_0108, g32p_row04_traceSegment_090_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_090 864 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 864 216 216, g32p_row04_traceSegment_090_0864_0216, g32p_row04_traceSegment_090_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1296 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1296 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1296 13 14, g32p_row04_traceSegment_090_1296_0013, g32p_row04_traceSegment_090_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1323 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1336 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1323 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1323 13 14, g32p_row04_traceSegment_090_1323_0013, g32p_row04_traceSegment_090_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1296 54 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1296 27 27, g32p_row04_traceSegment_090_1296_0027, g32p_row04_traceSegment_090_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1350 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1363 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1350 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1350 13 14, g32p_row04_traceSegment_090_1350_0013, g32p_row04_traceSegment_090_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1377 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1377 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1377 13 14, g32p_row04_traceSegment_090_1377_0013, g32p_row04_traceSegment_090_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1350 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1350 27 27, g32p_row04_traceSegment_090_1350_0027, g32p_row04_traceSegment_090_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 1296 108 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1296 54 54, g32p_row04_traceSegment_090_1296_0054, g32p_row04_traceSegment_090_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1404 13 14, g32p_row04_traceSegment_090_1404_0013, g32p_row04_traceSegment_090_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1431 13 14, g32p_row04_traceSegment_090_1431_0013, g32p_row04_traceSegment_090_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1404 27 27, g32p_row04_traceSegment_090_1404_0027, g32p_row04_traceSegment_090_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1458 13 14, g32p_row04_traceSegment_090_1458_0013, g32p_row04_traceSegment_090_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1485 13 14, g32p_row04_traceSegment_090_1485_0013, g32p_row04_traceSegment_090_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1458 27 27, g32p_row04_traceSegment_090_1458_0027, g32p_row04_traceSegment_090_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1404 54 54, g32p_row04_traceSegment_090_1404_0054, g32p_row04_traceSegment_090_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_090 1296 216 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1296 108 108, g32p_row04_traceSegment_090_1296_0108, g32p_row04_traceSegment_090_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1512 13 14, g32p_row04_traceSegment_090_1512_0013, g32p_row04_traceSegment_090_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1539 13 14, g32p_row04_traceSegment_090_1539_0013, g32p_row04_traceSegment_090_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1512 27 27, g32p_row04_traceSegment_090_1512_0027, g32p_row04_traceSegment_090_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1566 13 14, g32p_row04_traceSegment_090_1566_0013, g32p_row04_traceSegment_090_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1593 13 14, g32p_row04_traceSegment_090_1593_0013, g32p_row04_traceSegment_090_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1566 27 27, g32p_row04_traceSegment_090_1566_0027, g32p_row04_traceSegment_090_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1512 54 54, g32p_row04_traceSegment_090_1512_0054, g32p_row04_traceSegment_090_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1620 13 14, g32p_row04_traceSegment_090_1620_0013, g32p_row04_traceSegment_090_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1647 13 14, g32p_row04_traceSegment_090_1647_0013, g32p_row04_traceSegment_090_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1620 27 27, g32p_row04_traceSegment_090_1620_0027, g32p_row04_traceSegment_090_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1674 13 14, g32p_row04_traceSegment_090_1674_0013, g32p_row04_traceSegment_090_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_090 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_090 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_090_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_090 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1701 13 14, g32p_row04_traceSegment_090_1701_0013, g32p_row04_traceSegment_090_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_090 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1674 27 27, g32p_row04_traceSegment_090_1674_0027, g32p_row04_traceSegment_090_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_090 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1620 54 54, g32p_row04_traceSegment_090_1620_0054, g32p_row04_traceSegment_090_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_090 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1512 108 108, g32p_row04_traceSegment_090_1512_0108, g32p_row04_traceSegment_090_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_090_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_090 1296 432 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 1296 216 216, g32p_row04_traceSegment_090_1296_0216, g32p_row04_traceSegment_090_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_090 864 864 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 864 432 432, g32p_row04_traceSegment_090_0864_0432, g32p_row04_traceSegment_090_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_090_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_090 0 1728 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_090 0 864 864, g32p_row04_traceSegment_090_0000_0864, g32p_row04_traceSegment_090_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 90 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_090_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_091 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 91 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_091_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 0 13 14, g32p_row04_traceSegment_091_0000_0013, g32p_row04_traceSegment_091_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 27 13 14, g32p_row04_traceSegment_091_0027_0013, g32p_row04_traceSegment_091_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 0 27 27, g32p_row04_traceSegment_091_0000_0027, g32p_row04_traceSegment_091_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 54 13 14, g32p_row04_traceSegment_091_0054_0013, g32p_row04_traceSegment_091_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 81 13 14, g32p_row04_traceSegment_091_0081_0013, g32p_row04_traceSegment_091_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 54 27 27, g32p_row04_traceSegment_091_0054_0027, g32p_row04_traceSegment_091_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 0 54 54, g32p_row04_traceSegment_091_0000_0054, g32p_row04_traceSegment_091_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 108 13 14, g32p_row04_traceSegment_091_0108_0013, g32p_row04_traceSegment_091_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 135 13 14, g32p_row04_traceSegment_091_0135_0013, g32p_row04_traceSegment_091_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 108 27 27, g32p_row04_traceSegment_091_0108_0027, g32p_row04_traceSegment_091_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 162 13 14, g32p_row04_traceSegment_091_0162_0013, g32p_row04_traceSegment_091_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 189 13 14, g32p_row04_traceSegment_091_0189_0013, g32p_row04_traceSegment_091_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 162 27 27, g32p_row04_traceSegment_091_0162_0027, g32p_row04_traceSegment_091_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 108 54 54, g32p_row04_traceSegment_091_0108_0054, g32p_row04_traceSegment_091_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_091 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 0 108 108, g32p_row04_traceSegment_091_0000_0108, g32p_row04_traceSegment_091_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 216 13 14, g32p_row04_traceSegment_091_0216_0013, g32p_row04_traceSegment_091_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 243 13 14, g32p_row04_traceSegment_091_0243_0013, g32p_row04_traceSegment_091_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 216 27 27, g32p_row04_traceSegment_091_0216_0027, g32p_row04_traceSegment_091_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 270 13 14, g32p_row04_traceSegment_091_0270_0013, g32p_row04_traceSegment_091_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 297 13 14, g32p_row04_traceSegment_091_0297_0013, g32p_row04_traceSegment_091_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 270 27 27, g32p_row04_traceSegment_091_0270_0027, g32p_row04_traceSegment_091_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 216 54 54, g32p_row04_traceSegment_091_0216_0054, g32p_row04_traceSegment_091_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 324 13 14, g32p_row04_traceSegment_091_0324_0013, g32p_row04_traceSegment_091_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 351 13 14, g32p_row04_traceSegment_091_0351_0013, g32p_row04_traceSegment_091_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 324 27 27, g32p_row04_traceSegment_091_0324_0027, g32p_row04_traceSegment_091_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 378 13 14, g32p_row04_traceSegment_091_0378_0013, g32p_row04_traceSegment_091_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 405 13 14, g32p_row04_traceSegment_091_0405_0013, g32p_row04_traceSegment_091_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 378 27 27, g32p_row04_traceSegment_091_0378_0027, g32p_row04_traceSegment_091_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 324 54 54, g32p_row04_traceSegment_091_0324_0054, g32p_row04_traceSegment_091_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_091 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 216 108 108, g32p_row04_traceSegment_091_0216_0108, g32p_row04_traceSegment_091_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_091 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 0 216 216, g32p_row04_traceSegment_091_0000_0216, g32p_row04_traceSegment_091_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 432 13 14, g32p_row04_traceSegment_091_0432_0013, g32p_row04_traceSegment_091_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 459 13 14, g32p_row04_traceSegment_091_0459_0013, g32p_row04_traceSegment_091_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 432 27 27, g32p_row04_traceSegment_091_0432_0027, g32p_row04_traceSegment_091_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 486 13 14, g32p_row04_traceSegment_091_0486_0013, g32p_row04_traceSegment_091_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 513 13 14, g32p_row04_traceSegment_091_0513_0013, g32p_row04_traceSegment_091_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 486 27 27, g32p_row04_traceSegment_091_0486_0027, g32p_row04_traceSegment_091_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 432 54 54, g32p_row04_traceSegment_091_0432_0054, g32p_row04_traceSegment_091_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 540 13 14, g32p_row04_traceSegment_091_0540_0013, g32p_row04_traceSegment_091_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 567 13 14, g32p_row04_traceSegment_091_0567_0013, g32p_row04_traceSegment_091_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 540 27 27, g32p_row04_traceSegment_091_0540_0027, g32p_row04_traceSegment_091_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 594 13 14, g32p_row04_traceSegment_091_0594_0013, g32p_row04_traceSegment_091_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 621 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 621 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 621 13 14, g32p_row04_traceSegment_091_0621_0013, g32p_row04_traceSegment_091_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 594 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 594 27 27, g32p_row04_traceSegment_091_0594_0027, g32p_row04_traceSegment_091_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 540 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 540 54 54, g32p_row04_traceSegment_091_0540_0054, g32p_row04_traceSegment_091_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_091 432 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 432 108 108, g32p_row04_traceSegment_091_0432_0108, g32p_row04_traceSegment_091_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 648 13 14, g32p_row04_traceSegment_091_0648_0013, g32p_row04_traceSegment_091_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 675 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 675 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 675 13 14, g32p_row04_traceSegment_091_0675_0013, g32p_row04_traceSegment_091_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 648 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 648 27 27, g32p_row04_traceSegment_091_0648_0027, g32p_row04_traceSegment_091_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 702 13 14, g32p_row04_traceSegment_091_0702_0013, g32p_row04_traceSegment_091_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 729 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 729 27 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 729 13 14, g32p_row04_traceSegment_091_0729_0013, g32p_row04_traceSegment_091_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 702 54 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 702 27 27, g32p_row04_traceSegment_091_0702_0027, g32p_row04_traceSegment_091_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 648 108 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 648 54 54, g32p_row04_traceSegment_091_0648_0054, g32p_row04_traceSegment_091_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 756 13 14, g32p_row04_traceSegment_091_0756_0013, g32p_row04_traceSegment_091_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 796 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 783 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 783 13 14, g32p_row04_traceSegment_091_0783_0013, g32p_row04_traceSegment_091_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 756 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 756 27 27, g32p_row04_traceSegment_091_0756_0027, g32p_row04_traceSegment_091_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 810 13 14, g32p_row04_traceSegment_091_0810_0013, g32p_row04_traceSegment_091_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 837 13 14, g32p_row04_traceSegment_091_0837_0013, g32p_row04_traceSegment_091_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 810 27 27, g32p_row04_traceSegment_091_0810_0027, g32p_row04_traceSegment_091_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 756 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 756 54 54, g32p_row04_traceSegment_091_0756_0054, g32p_row04_traceSegment_091_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_091 648 216 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 648 108 108, g32p_row04_traceSegment_091_0648_0108, g32p_row04_traceSegment_091_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_091 432 432 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 432 216 216, g32p_row04_traceSegment_091_0432_0216, g32p_row04_traceSegment_091_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_091 0 864 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 0 432 432, g32p_row04_traceSegment_091_0000_0432, g32p_row04_traceSegment_091_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 864 13 14, g32p_row04_traceSegment_091_0864_0013, g32p_row04_traceSegment_091_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 891 13 14, g32p_row04_traceSegment_091_0891_0013, g32p_row04_traceSegment_091_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 864 27 27, g32p_row04_traceSegment_091_0864_0027, g32p_row04_traceSegment_091_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 918 13 14, g32p_row04_traceSegment_091_0918_0013, g32p_row04_traceSegment_091_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 945 13 14, g32p_row04_traceSegment_091_0945_0013, g32p_row04_traceSegment_091_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 918 27 27, g32p_row04_traceSegment_091_0918_0027, g32p_row04_traceSegment_091_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 864 54 54, g32p_row04_traceSegment_091_0864_0054, g32p_row04_traceSegment_091_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 972 13 14, g32p_row04_traceSegment_091_0972_0013, g32p_row04_traceSegment_091_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 999 13 14, g32p_row04_traceSegment_091_0999_0013, g32p_row04_traceSegment_091_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 972 27 27, g32p_row04_traceSegment_091_0972_0027, g32p_row04_traceSegment_091_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1026 13 14, g32p_row04_traceSegment_091_1026_0013, g32p_row04_traceSegment_091_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1053 13 14, g32p_row04_traceSegment_091_1053_0013, g32p_row04_traceSegment_091_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1026 27 27, g32p_row04_traceSegment_091_1026_0027, g32p_row04_traceSegment_091_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 972 54 54, g32p_row04_traceSegment_091_0972_0054, g32p_row04_traceSegment_091_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_091 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 864 108 108, g32p_row04_traceSegment_091_0864_0108, g32p_row04_traceSegment_091_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1080 13 14, g32p_row04_traceSegment_091_1080_0013, g32p_row04_traceSegment_091_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1107 13 14, g32p_row04_traceSegment_091_1107_0013, g32p_row04_traceSegment_091_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1080 27 27, g32p_row04_traceSegment_091_1080_0027, g32p_row04_traceSegment_091_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1134 13 14, g32p_row04_traceSegment_091_1134_0013, g32p_row04_traceSegment_091_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1161 13 14, g32p_row04_traceSegment_091_1161_0013, g32p_row04_traceSegment_091_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1134 27 27, g32p_row04_traceSegment_091_1134_0027, g32p_row04_traceSegment_091_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1080 54 54, g32p_row04_traceSegment_091_1080_0054, g32p_row04_traceSegment_091_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1188 13 14, g32p_row04_traceSegment_091_1188_0013, g32p_row04_traceSegment_091_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1215 13 14, g32p_row04_traceSegment_091_1215_0013, g32p_row04_traceSegment_091_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1188 27 27, g32p_row04_traceSegment_091_1188_0027, g32p_row04_traceSegment_091_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1242 13 14, g32p_row04_traceSegment_091_1242_0013, g32p_row04_traceSegment_091_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1269 13 14, g32p_row04_traceSegment_091_1269_0013, g32p_row04_traceSegment_091_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1242 27 27, g32p_row04_traceSegment_091_1242_0027, g32p_row04_traceSegment_091_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1188 54 54, g32p_row04_traceSegment_091_1188_0054, g32p_row04_traceSegment_091_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_091 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1080 108 108, g32p_row04_traceSegment_091_1080_0108, g32p_row04_traceSegment_091_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_091 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 864 216 216, g32p_row04_traceSegment_091_0864_0216, g32p_row04_traceSegment_091_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1296 13 14, g32p_row04_traceSegment_091_1296_0013, g32p_row04_traceSegment_091_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1323 13 14, g32p_row04_traceSegment_091_1323_0013, g32p_row04_traceSegment_091_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1296 27 27, g32p_row04_traceSegment_091_1296_0027, g32p_row04_traceSegment_091_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1350 13 14, g32p_row04_traceSegment_091_1350_0013, g32p_row04_traceSegment_091_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1377 13 14, g32p_row04_traceSegment_091_1377_0013, g32p_row04_traceSegment_091_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1350 27 27, g32p_row04_traceSegment_091_1350_0027, g32p_row04_traceSegment_091_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1296 54 54, g32p_row04_traceSegment_091_1296_0054, g32p_row04_traceSegment_091_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1404 13 14, g32p_row04_traceSegment_091_1404_0013, g32p_row04_traceSegment_091_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1431 13 14, g32p_row04_traceSegment_091_1431_0013, g32p_row04_traceSegment_091_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1404 27 27, g32p_row04_traceSegment_091_1404_0027, g32p_row04_traceSegment_091_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1458 13 14, g32p_row04_traceSegment_091_1458_0013, g32p_row04_traceSegment_091_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1485 13 14, g32p_row04_traceSegment_091_1485_0013, g32p_row04_traceSegment_091_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1458 27 27, g32p_row04_traceSegment_091_1458_0027, g32p_row04_traceSegment_091_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1404 54 54, g32p_row04_traceSegment_091_1404_0054, g32p_row04_traceSegment_091_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_091 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1296 108 108, g32p_row04_traceSegment_091_1296_0108, g32p_row04_traceSegment_091_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1525 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1512 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1512 13 14, g32p_row04_traceSegment_091_1512_0013, g32p_row04_traceSegment_091_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1539 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1539 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1539 13 14, g32p_row04_traceSegment_091_1539_0013, g32p_row04_traceSegment_091_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1512 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1512 27 27, g32p_row04_traceSegment_091_1512_0027, g32p_row04_traceSegment_091_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1566 13 14, g32p_row04_traceSegment_091_1566_0013, g32p_row04_traceSegment_091_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1593 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1593 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1593 13 14, g32p_row04_traceSegment_091_1593_0013, g32p_row04_traceSegment_091_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1566 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1566 27 27, g32p_row04_traceSegment_091_1566_0027, g32p_row04_traceSegment_091_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 1512 108 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1512 54 54, g32p_row04_traceSegment_091_1512_0054, g32p_row04_traceSegment_091_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1620 13 14, g32p_row04_traceSegment_091_1620_0013, g32p_row04_traceSegment_091_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1647 13 14, g32p_row04_traceSegment_091_1647_0013, g32p_row04_traceSegment_091_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1620 27 27, g32p_row04_traceSegment_091_1620_0027, g32p_row04_traceSegment_091_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1674 13 14, g32p_row04_traceSegment_091_1674_0013, g32p_row04_traceSegment_091_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_091 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_091 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_091_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_091 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1701 13 14, g32p_row04_traceSegment_091_1701_0013, g32p_row04_traceSegment_091_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_091 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1674 27 27, g32p_row04_traceSegment_091_1674_0027, g32p_row04_traceSegment_091_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_091 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1620 54 54, g32p_row04_traceSegment_091_1620_0054, g32p_row04_traceSegment_091_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_091 1512 216 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1512 108 108, g32p_row04_traceSegment_091_1512_0108, g32p_row04_traceSegment_091_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_091_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_091 1296 432 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 1296 216 216, g32p_row04_traceSegment_091_1296_0216, g32p_row04_traceSegment_091_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_091 864 864 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 864 432 432, g32p_row04_traceSegment_091_0864_0432, g32p_row04_traceSegment_091_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_091_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_091 0 1728 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_091 0 864 864, g32p_row04_traceSegment_091_0000_0864, g32p_row04_traceSegment_091_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 91 = [0, 4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_091_0000_1728

end HodgeLean.Foundations.Program

end
end
