import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0191
import HodgeLean.Foundations.Program.G32PropFourSixPacked0187
import HodgeLean.Foundations.Program.G32PropFourSixPacked0293
import HodgeLean.Foundations.Program.G32PropFourSixPacked0295
import HodgeLean.Foundations.Program.G32PropFourSixPacked0297
import HodgeLean.Foundations.Program.G32PropFourSixPacked0299
import HodgeLean.Foundations.Program.G32PropFourSixPacked0301
import HodgeLean.Foundations.Program.G32PropFourSixPacked0303
import HodgeLean.Foundations.Program.G32PropFourSixPacked0305
import HodgeLean.Foundations.Program.G32PropFourSixPacked0307
import HodgeLean.Foundations.Program.G32PropFourSixPacked0309
import HodgeLean.Foundations.Program.G32PropFourSixPacked0311
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixPacked0192
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_098 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 98 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_098_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 0 13 14, g32p_row02_traceSegment_098_0000_0013, g32p_row02_traceSegment_098_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 27 13 14, g32p_row02_traceSegment_098_0027_0013, g32p_row02_traceSegment_098_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 0 27 27, g32p_row02_traceSegment_098_0000_0027, g32p_row02_traceSegment_098_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 54 13 14, g32p_row02_traceSegment_098_0054_0013, g32p_row02_traceSegment_098_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 81 13 14, g32p_row02_traceSegment_098_0081_0013, g32p_row02_traceSegment_098_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 54 27 27, g32p_row02_traceSegment_098_0054_0027, g32p_row02_traceSegment_098_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 0 54 54, g32p_row02_traceSegment_098_0000_0054, g32p_row02_traceSegment_098_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 108 13 14, g32p_row02_traceSegment_098_0108_0013, g32p_row02_traceSegment_098_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 135 13 14, g32p_row02_traceSegment_098_0135_0013, g32p_row02_traceSegment_098_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 108 27 27, g32p_row02_traceSegment_098_0108_0027, g32p_row02_traceSegment_098_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 162 13 14, g32p_row02_traceSegment_098_0162_0013, g32p_row02_traceSegment_098_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 202 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 189 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 189 13 14, g32p_row02_traceSegment_098_0189_0013, g32p_row02_traceSegment_098_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 162 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 162 27 27, g32p_row02_traceSegment_098_0162_0027, g32p_row02_traceSegment_098_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 108 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 108 54 54, g32p_row02_traceSegment_098_0108_0054, g32p_row02_traceSegment_098_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 0 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 0 108 108, g32p_row02_traceSegment_098_0000_0108, g32p_row02_traceSegment_098_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 216 13 14, g32p_row02_traceSegment_098_0216_0013, g32p_row02_traceSegment_098_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 243 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 243 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 243 13 14, g32p_row02_traceSegment_098_0243_0013, g32p_row02_traceSegment_098_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 216 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 216 27 27, g32p_row02_traceSegment_098_0216_0027, g32p_row02_traceSegment_098_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 270 13 14, g32p_row02_traceSegment_098_0270_0013, g32p_row02_traceSegment_098_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 297 13 14, g32p_row02_traceSegment_098_0297_0013, g32p_row02_traceSegment_098_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 270 27 27, g32p_row02_traceSegment_098_0270_0027, g32p_row02_traceSegment_098_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 216 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 216 54 54, g32p_row02_traceSegment_098_0216_0054, g32p_row02_traceSegment_098_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 324 13 14, g32p_row02_traceSegment_098_0324_0013, g32p_row02_traceSegment_098_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 351 13 14, g32p_row02_traceSegment_098_0351_0013, g32p_row02_traceSegment_098_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 324 27 27, g32p_row02_traceSegment_098_0324_0027, g32p_row02_traceSegment_098_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 378 13 14, g32p_row02_traceSegment_098_0378_0013, g32p_row02_traceSegment_098_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 405 13 14, g32p_row02_traceSegment_098_0405_0013, g32p_row02_traceSegment_098_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 378 27 27, g32p_row02_traceSegment_098_0378_0027, g32p_row02_traceSegment_098_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 324 54 54, g32p_row02_traceSegment_098_0324_0054, g32p_row02_traceSegment_098_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 216 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 216 108 108, g32p_row02_traceSegment_098_0216_0108, g32p_row02_traceSegment_098_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_098 0 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 0 216 216, g32p_row02_traceSegment_098_0000_0216, g32p_row02_traceSegment_098_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 432 13 14, g32p_row02_traceSegment_098_0432_0013, g32p_row02_traceSegment_098_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 459 13 14, g32p_row02_traceSegment_098_0459_0013, g32p_row02_traceSegment_098_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 432 27 27, g32p_row02_traceSegment_098_0432_0027, g32p_row02_traceSegment_098_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 486 13 14, g32p_row02_traceSegment_098_0486_0013, g32p_row02_traceSegment_098_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 513 13 14, g32p_row02_traceSegment_098_0513_0013, g32p_row02_traceSegment_098_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 486 27 27, g32p_row02_traceSegment_098_0486_0027, g32p_row02_traceSegment_098_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 432 54 54, g32p_row02_traceSegment_098_0432_0054, g32p_row02_traceSegment_098_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 540 13 14, g32p_row02_traceSegment_098_0540_0013, g32p_row02_traceSegment_098_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 567 13 14, g32p_row02_traceSegment_098_0567_0013, g32p_row02_traceSegment_098_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 540 27 27, g32p_row02_traceSegment_098_0540_0027, g32p_row02_traceSegment_098_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 594 13 14, g32p_row02_traceSegment_098_0594_0013, g32p_row02_traceSegment_098_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 621 13 14, g32p_row02_traceSegment_098_0621_0013, g32p_row02_traceSegment_098_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 594 27 27, g32p_row02_traceSegment_098_0594_0027, g32p_row02_traceSegment_098_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 540 54 54, g32p_row02_traceSegment_098_0540_0054, g32p_row02_traceSegment_098_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 432 108 108, g32p_row02_traceSegment_098_0432_0108, g32p_row02_traceSegment_098_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 648 13 14, g32p_row02_traceSegment_098_0648_0013, g32p_row02_traceSegment_098_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 675 13 14, g32p_row02_traceSegment_098_0675_0013, g32p_row02_traceSegment_098_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 648 27 27, g32p_row02_traceSegment_098_0648_0027, g32p_row02_traceSegment_098_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 702 13 14, g32p_row02_traceSegment_098_0702_0013, g32p_row02_traceSegment_098_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 729 13 14, g32p_row02_traceSegment_098_0729_0013, g32p_row02_traceSegment_098_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 702 27 27, g32p_row02_traceSegment_098_0702_0027, g32p_row02_traceSegment_098_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 648 54 54, g32p_row02_traceSegment_098_0648_0054, g32p_row02_traceSegment_098_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 756 13 14, g32p_row02_traceSegment_098_0756_0013, g32p_row02_traceSegment_098_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 783 13 14, g32p_row02_traceSegment_098_0783_0013, g32p_row02_traceSegment_098_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 756 27 27, g32p_row02_traceSegment_098_0756_0027, g32p_row02_traceSegment_098_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 810 13 14, g32p_row02_traceSegment_098_0810_0013, g32p_row02_traceSegment_098_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 837 13 14, g32p_row02_traceSegment_098_0837_0013, g32p_row02_traceSegment_098_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 810 27 27, g32p_row02_traceSegment_098_0810_0027, g32p_row02_traceSegment_098_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 756 54 54, g32p_row02_traceSegment_098_0756_0054, g32p_row02_traceSegment_098_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 648 108 108, g32p_row02_traceSegment_098_0648_0108, g32p_row02_traceSegment_098_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_098 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 432 216 216, g32p_row02_traceSegment_098_0432_0216, g32p_row02_traceSegment_098_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_098 0 864 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 0 432 432, g32p_row02_traceSegment_098_0000_0432, g32p_row02_traceSegment_098_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 864 13 14, g32p_row02_traceSegment_098_0864_0013, g32p_row02_traceSegment_098_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 904 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 891 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 891 13 14, g32p_row02_traceSegment_098_0891_0013, g32p_row02_traceSegment_098_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 864 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 864 27 27, g32p_row02_traceSegment_098_0864_0027, g32p_row02_traceSegment_098_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 918 13 14, g32p_row02_traceSegment_098_0918_0013, g32p_row02_traceSegment_098_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 945 13 14, g32p_row02_traceSegment_098_0945_0013, g32p_row02_traceSegment_098_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 918 27 27, g32p_row02_traceSegment_098_0918_0027, g32p_row02_traceSegment_098_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 864 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 864 54 54, g32p_row02_traceSegment_098_0864_0054, g32p_row02_traceSegment_098_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 972 13 14, g32p_row02_traceSegment_098_0972_0013, g32p_row02_traceSegment_098_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 999 13 14, g32p_row02_traceSegment_098_0999_0013, g32p_row02_traceSegment_098_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 972 27 27, g32p_row02_traceSegment_098_0972_0027, g32p_row02_traceSegment_098_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1026 13 14, g32p_row02_traceSegment_098_1026_0013, g32p_row02_traceSegment_098_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1053 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1053 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1053 13 14, g32p_row02_traceSegment_098_1053_0013, g32p_row02_traceSegment_098_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1026 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1026 27 27, g32p_row02_traceSegment_098_1026_0027, g32p_row02_traceSegment_098_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 972 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 972 54 54, g32p_row02_traceSegment_098_0972_0054, g32p_row02_traceSegment_098_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 864 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 864 108 108, g32p_row02_traceSegment_098_0864_0108, g32p_row02_traceSegment_098_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1080 13 14, g32p_row02_traceSegment_098_1080_0013, g32p_row02_traceSegment_098_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1107 13 14, g32p_row02_traceSegment_098_1107_0013, g32p_row02_traceSegment_098_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1080 27 27, g32p_row02_traceSegment_098_1080_0027, g32p_row02_traceSegment_098_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1134 13 14, g32p_row02_traceSegment_098_1134_0013, g32p_row02_traceSegment_098_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1161 13 14, g32p_row02_traceSegment_098_1161_0013, g32p_row02_traceSegment_098_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1134 27 27, g32p_row02_traceSegment_098_1134_0027, g32p_row02_traceSegment_098_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1080 54 54, g32p_row02_traceSegment_098_1080_0054, g32p_row02_traceSegment_098_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1188 13 14, g32p_row02_traceSegment_098_1188_0013, g32p_row02_traceSegment_098_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1215 13 14, g32p_row02_traceSegment_098_1215_0013, g32p_row02_traceSegment_098_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1188 27 27, g32p_row02_traceSegment_098_1188_0027, g32p_row02_traceSegment_098_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1242 13 14, g32p_row02_traceSegment_098_1242_0013, g32p_row02_traceSegment_098_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1269 13 14, g32p_row02_traceSegment_098_1269_0013, g32p_row02_traceSegment_098_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1242 27 27, g32p_row02_traceSegment_098_1242_0027, g32p_row02_traceSegment_098_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1188 54 54, g32p_row02_traceSegment_098_1188_0054, g32p_row02_traceSegment_098_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1080 108 108, g32p_row02_traceSegment_098_1080_0108, g32p_row02_traceSegment_098_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_098 864 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 864 216 216, g32p_row02_traceSegment_098_0864_0216, g32p_row02_traceSegment_098_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1296 13 14, g32p_row02_traceSegment_098_1296_0013, g32p_row02_traceSegment_098_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1323 13 14, g32p_row02_traceSegment_098_1323_0013, g32p_row02_traceSegment_098_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1296 27 27, g32p_row02_traceSegment_098_1296_0027, g32p_row02_traceSegment_098_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1350 13 14, g32p_row02_traceSegment_098_1350_0013, g32p_row02_traceSegment_098_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1377 13 14, g32p_row02_traceSegment_098_1377_0013, g32p_row02_traceSegment_098_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1350 27 27, g32p_row02_traceSegment_098_1350_0027, g32p_row02_traceSegment_098_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1296 54 54, g32p_row02_traceSegment_098_1296_0054, g32p_row02_traceSegment_098_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1404 13 14, g32p_row02_traceSegment_098_1404_0013, g32p_row02_traceSegment_098_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1431 13 14, g32p_row02_traceSegment_098_1431_0013, g32p_row02_traceSegment_098_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1404 27 27, g32p_row02_traceSegment_098_1404_0027, g32p_row02_traceSegment_098_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1458 13 14, g32p_row02_traceSegment_098_1458_0013, g32p_row02_traceSegment_098_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1485 13 14, g32p_row02_traceSegment_098_1485_0013, g32p_row02_traceSegment_098_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1458 27 27, g32p_row02_traceSegment_098_1458_0027, g32p_row02_traceSegment_098_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1404 54 54, g32p_row02_traceSegment_098_1404_0054, g32p_row02_traceSegment_098_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1296 108 108, g32p_row02_traceSegment_098_1296_0108, g32p_row02_traceSegment_098_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1512 13 14, g32p_row02_traceSegment_098_1512_0013, g32p_row02_traceSegment_098_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1539 13 14, g32p_row02_traceSegment_098_1539_0013, g32p_row02_traceSegment_098_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1512 27 27, g32p_row02_traceSegment_098_1512_0027, g32p_row02_traceSegment_098_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1566 13 14, g32p_row02_traceSegment_098_1566_0013, g32p_row02_traceSegment_098_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1593 13 14, g32p_row02_traceSegment_098_1593_0013, g32p_row02_traceSegment_098_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1566 27 27, g32p_row02_traceSegment_098_1566_0027, g32p_row02_traceSegment_098_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1512 54 54, g32p_row02_traceSegment_098_1512_0054, g32p_row02_traceSegment_098_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1620 13 14, g32p_row02_traceSegment_098_1620_0013, g32p_row02_traceSegment_098_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1647 13 14, g32p_row02_traceSegment_098_1647_0013, g32p_row02_traceSegment_098_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1620 27 27, g32p_row02_traceSegment_098_1620_0027, g32p_row02_traceSegment_098_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1674 13 14, g32p_row02_traceSegment_098_1674_0013, g32p_row02_traceSegment_098_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1701 13 14, g32p_row02_traceSegment_098_1701_0013, g32p_row02_traceSegment_098_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1674 27 27, g32p_row02_traceSegment_098_1674_0027, g32p_row02_traceSegment_098_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1620 54 54, g32p_row02_traceSegment_098_1620_0054, g32p_row02_traceSegment_098_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1512 108 108, g32p_row02_traceSegment_098_1512_0108, g32p_row02_traceSegment_098_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_098 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1296 216 216, g32p_row02_traceSegment_098_1296_0216, g32p_row02_traceSegment_098_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_098 864 864 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 864 432 432, g32p_row02_traceSegment_098_0864_0432, g32p_row02_traceSegment_098_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_098 0 1728 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 0 864 864, g32p_row02_traceSegment_098_0000_0864, g32p_row02_traceSegment_098_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1728 13 14, g32p_row02_traceSegment_098_1728_0013, g32p_row02_traceSegment_098_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1755 13 14, g32p_row02_traceSegment_098_1755_0013, g32p_row02_traceSegment_098_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1728 27 27, g32p_row02_traceSegment_098_1728_0027, g32p_row02_traceSegment_098_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1782 13 14, g32p_row02_traceSegment_098_1782_0013, g32p_row02_traceSegment_098_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1809 13 14, g32p_row02_traceSegment_098_1809_0013, g32p_row02_traceSegment_098_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1782 27 27, g32p_row02_traceSegment_098_1782_0027, g32p_row02_traceSegment_098_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1728 54 54, g32p_row02_traceSegment_098_1728_0054, g32p_row02_traceSegment_098_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1836 13 14, g32p_row02_traceSegment_098_1836_0013, g32p_row02_traceSegment_098_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1863 13 14, g32p_row02_traceSegment_098_1863_0013, g32p_row02_traceSegment_098_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1836 27 27, g32p_row02_traceSegment_098_1836_0027, g32p_row02_traceSegment_098_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1890 13 14, g32p_row02_traceSegment_098_1890_0013, g32p_row02_traceSegment_098_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1917 13 14, g32p_row02_traceSegment_098_1917_0013, g32p_row02_traceSegment_098_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1890 27 27, g32p_row02_traceSegment_098_1890_0027, g32p_row02_traceSegment_098_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1836 54 54, g32p_row02_traceSegment_098_1836_0054, g32p_row02_traceSegment_098_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1728 108 108, g32p_row02_traceSegment_098_1728_0108, g32p_row02_traceSegment_098_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1944 13 14, g32p_row02_traceSegment_098_1944_0013, g32p_row02_traceSegment_098_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1971 13 14, g32p_row02_traceSegment_098_1971_0013, g32p_row02_traceSegment_098_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1944 27 27, g32p_row02_traceSegment_098_1944_0027, g32p_row02_traceSegment_098_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1998 13 14, g32p_row02_traceSegment_098_1998_0013, g32p_row02_traceSegment_098_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2025 13 14, g32p_row02_traceSegment_098_2025_0013, g32p_row02_traceSegment_098_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1998 27 27, g32p_row02_traceSegment_098_1998_0027, g32p_row02_traceSegment_098_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1944 54 54, g32p_row02_traceSegment_098_1944_0054, g32p_row02_traceSegment_098_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2052 13 14, g32p_row02_traceSegment_098_2052_0013, g32p_row02_traceSegment_098_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2079 13 14, g32p_row02_traceSegment_098_2079_0013, g32p_row02_traceSegment_098_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2052 27 27, g32p_row02_traceSegment_098_2052_0027, g32p_row02_traceSegment_098_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2106 13 14, g32p_row02_traceSegment_098_2106_0013, g32p_row02_traceSegment_098_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2133 13 14, g32p_row02_traceSegment_098_2133_0013, g32p_row02_traceSegment_098_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2106 27 27, g32p_row02_traceSegment_098_2106_0027, g32p_row02_traceSegment_098_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2052 54 54, g32p_row02_traceSegment_098_2052_0054, g32p_row02_traceSegment_098_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1944 108 108, g32p_row02_traceSegment_098_1944_0108, g32p_row02_traceSegment_098_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_098 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1728 216 216, g32p_row02_traceSegment_098_1728_0216, g32p_row02_traceSegment_098_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2173 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2160 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2160 13 14, g32p_row02_traceSegment_098_2160_0013, g32p_row02_traceSegment_098_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2187 13 14, g32p_row02_traceSegment_098_2187_0013, g32p_row02_traceSegment_098_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2160 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2160 27 27, g32p_row02_traceSegment_098_2160_0027, g32p_row02_traceSegment_098_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2227 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2214 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2214 13 14, g32p_row02_traceSegment_098_2214_0013, g32p_row02_traceSegment_098_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2241 13 14, g32p_row02_traceSegment_098_2241_0013, g32p_row02_traceSegment_098_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2214 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2214 27 27, g32p_row02_traceSegment_098_2214_0027, g32p_row02_traceSegment_098_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 2160 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2160 54 54, g32p_row02_traceSegment_098_2160_0054, g32p_row02_traceSegment_098_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2268 13 14, g32p_row02_traceSegment_098_2268_0013, g32p_row02_traceSegment_098_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2295 13 14, g32p_row02_traceSegment_098_2295_0013, g32p_row02_traceSegment_098_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2268 27 27, g32p_row02_traceSegment_098_2268_0027, g32p_row02_traceSegment_098_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2322 13 14, g32p_row02_traceSegment_098_2322_0013, g32p_row02_traceSegment_098_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2349 13 14, g32p_row02_traceSegment_098_2349_0013, g32p_row02_traceSegment_098_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2322 27 27, g32p_row02_traceSegment_098_2322_0027, g32p_row02_traceSegment_098_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2268 54 54, g32p_row02_traceSegment_098_2268_0054, g32p_row02_traceSegment_098_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 2160 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2160 108 108, g32p_row02_traceSegment_098_2160_0108, g32p_row02_traceSegment_098_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2376 13 14, g32p_row02_traceSegment_098_2376_0013, g32p_row02_traceSegment_098_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2403 13 14, g32p_row02_traceSegment_098_2403_0013, g32p_row02_traceSegment_098_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2376 27 27, g32p_row02_traceSegment_098_2376_0027, g32p_row02_traceSegment_098_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2430 13 14, g32p_row02_traceSegment_098_2430_0013, g32p_row02_traceSegment_098_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2457 13 14, g32p_row02_traceSegment_098_2457_0013, g32p_row02_traceSegment_098_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2430 27 27, g32p_row02_traceSegment_098_2430_0027, g32p_row02_traceSegment_098_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2376 54 54, g32p_row02_traceSegment_098_2376_0054, g32p_row02_traceSegment_098_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2484 13 14, g32p_row02_traceSegment_098_2484_0013, g32p_row02_traceSegment_098_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2511 13 14, g32p_row02_traceSegment_098_2511_0013, g32p_row02_traceSegment_098_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2484 27 27, g32p_row02_traceSegment_098_2484_0027, g32p_row02_traceSegment_098_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2538 13 14, g32p_row02_traceSegment_098_2538_0013, g32p_row02_traceSegment_098_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2565 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2565 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2565 13 14, g32p_row02_traceSegment_098_2565_0013, g32p_row02_traceSegment_098_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2538 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2538 27 27, g32p_row02_traceSegment_098_2538_0027, g32p_row02_traceSegment_098_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 2484 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2484 54 54, g32p_row02_traceSegment_098_2484_0054, g32p_row02_traceSegment_098_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 2376 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2376 108 108, g32p_row02_traceSegment_098_2376_0108, g32p_row02_traceSegment_098_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_098 2160 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2160 216 216, g32p_row02_traceSegment_098_2160_0216, g32p_row02_traceSegment_098_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_098 1728 864 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1728 432 432, g32p_row02_traceSegment_098_1728_0432, g32p_row02_traceSegment_098_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2592 13 14, g32p_row02_traceSegment_098_2592_0013, g32p_row02_traceSegment_098_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2619 13 14, g32p_row02_traceSegment_098_2619_0013, g32p_row02_traceSegment_098_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2592 27 27, g32p_row02_traceSegment_098_2592_0027, g32p_row02_traceSegment_098_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2646 13 14, g32p_row02_traceSegment_098_2646_0013, g32p_row02_traceSegment_098_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2673 13 14, g32p_row02_traceSegment_098_2673_0013, g32p_row02_traceSegment_098_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2646 27 27, g32p_row02_traceSegment_098_2646_0027, g32p_row02_traceSegment_098_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2592 54 54, g32p_row02_traceSegment_098_2592_0054, g32p_row02_traceSegment_098_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2700 13 14, g32p_row02_traceSegment_098_2700_0013, g32p_row02_traceSegment_098_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2727 13 14, g32p_row02_traceSegment_098_2727_0013, g32p_row02_traceSegment_098_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2700 27 27, g32p_row02_traceSegment_098_2700_0027, g32p_row02_traceSegment_098_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2754 13 14, g32p_row02_traceSegment_098_2754_0013, g32p_row02_traceSegment_098_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2781 13 14, g32p_row02_traceSegment_098_2781_0013, g32p_row02_traceSegment_098_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2754 27 27, g32p_row02_traceSegment_098_2754_0027, g32p_row02_traceSegment_098_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2700 54 54, g32p_row02_traceSegment_098_2700_0054, g32p_row02_traceSegment_098_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2592 108 108, g32p_row02_traceSegment_098_2592_0108, g32p_row02_traceSegment_098_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2821 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2808 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2808 13 14, g32p_row02_traceSegment_098_2808_0013, g32p_row02_traceSegment_098_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2835 13 14, g32p_row02_traceSegment_098_2835_0013, g32p_row02_traceSegment_098_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2808 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2808 27 27, g32p_row02_traceSegment_098_2808_0027, g32p_row02_traceSegment_098_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2862 13 14, g32p_row02_traceSegment_098_2862_0013, g32p_row02_traceSegment_098_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2889 13 14, g32p_row02_traceSegment_098_2889_0013, g32p_row02_traceSegment_098_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2862 27 27, g32p_row02_traceSegment_098_2862_0027, g32p_row02_traceSegment_098_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 2808 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2808 54 54, g32p_row02_traceSegment_098_2808_0054, g32p_row02_traceSegment_098_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2916 13 14, g32p_row02_traceSegment_098_2916_0013, g32p_row02_traceSegment_098_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2943 13 14, g32p_row02_traceSegment_098_2943_0013, g32p_row02_traceSegment_098_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2916 27 27, g32p_row02_traceSegment_098_2916_0027, g32p_row02_traceSegment_098_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2970 13 14, g32p_row02_traceSegment_098_2970_0013, g32p_row02_traceSegment_098_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2997 13 14, g32p_row02_traceSegment_098_2997_0013, g32p_row02_traceSegment_098_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2970 27 27, g32p_row02_traceSegment_098_2970_0027, g32p_row02_traceSegment_098_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2916 54 54, g32p_row02_traceSegment_098_2916_0054, g32p_row02_traceSegment_098_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 2808 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2808 108 108, g32p_row02_traceSegment_098_2808_0108, g32p_row02_traceSegment_098_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_098 2592 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2592 216 216, g32p_row02_traceSegment_098_2592_0216, g32p_row02_traceSegment_098_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3024 13 14, g32p_row02_traceSegment_098_3024_0013, g32p_row02_traceSegment_098_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3051 13 14, g32p_row02_traceSegment_098_3051_0013, g32p_row02_traceSegment_098_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3024 27 27, g32p_row02_traceSegment_098_3024_0027, g32p_row02_traceSegment_098_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3078 13 14, g32p_row02_traceSegment_098_3078_0013, g32p_row02_traceSegment_098_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3105 13 14, g32p_row02_traceSegment_098_3105_0013, g32p_row02_traceSegment_098_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3078 27 27, g32p_row02_traceSegment_098_3078_0027, g32p_row02_traceSegment_098_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3024 54 54, g32p_row02_traceSegment_098_3024_0054, g32p_row02_traceSegment_098_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3132 13 14, g32p_row02_traceSegment_098_3132_0013, g32p_row02_traceSegment_098_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3159 13 14, g32p_row02_traceSegment_098_3159_0013, g32p_row02_traceSegment_098_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3132 27 27, g32p_row02_traceSegment_098_3132_0027, g32p_row02_traceSegment_098_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3186 13 14, g32p_row02_traceSegment_098_3186_0013, g32p_row02_traceSegment_098_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3213 13 14, g32p_row02_traceSegment_098_3213_0013, g32p_row02_traceSegment_098_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3186 27 27, g32p_row02_traceSegment_098_3186_0027, g32p_row02_traceSegment_098_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3132 54 54, g32p_row02_traceSegment_098_3132_0054, g32p_row02_traceSegment_098_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3024 108 108, g32p_row02_traceSegment_098_3024_0108, g32p_row02_traceSegment_098_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3240 13 14, g32p_row02_traceSegment_098_3240_0013, g32p_row02_traceSegment_098_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3267 13 14, g32p_row02_traceSegment_098_3267_0013, g32p_row02_traceSegment_098_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3240 27 27, g32p_row02_traceSegment_098_3240_0027, g32p_row02_traceSegment_098_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3294 13 14, g32p_row02_traceSegment_098_3294_0013, g32p_row02_traceSegment_098_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3321 13 14, g32p_row02_traceSegment_098_3321_0013, g32p_row02_traceSegment_098_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3294 27 27, g32p_row02_traceSegment_098_3294_0027, g32p_row02_traceSegment_098_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3240 54 54, g32p_row02_traceSegment_098_3240_0054, g32p_row02_traceSegment_098_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3348 13 14, g32p_row02_traceSegment_098_3348_0013, g32p_row02_traceSegment_098_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3375 13 14, g32p_row02_traceSegment_098_3375_0013, g32p_row02_traceSegment_098_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3348 27 27, g32p_row02_traceSegment_098_3348_0027, g32p_row02_traceSegment_098_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3402 13 14, g32p_row02_traceSegment_098_3402_0013, g32p_row02_traceSegment_098_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_098 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_098 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_098_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_098 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3429 13 14, g32p_row02_traceSegment_098_3429_0013, g32p_row02_traceSegment_098_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_098 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3402 27 27, g32p_row02_traceSegment_098_3402_0027, g32p_row02_traceSegment_098_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_098 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3348 54 54, g32p_row02_traceSegment_098_3348_0054, g32p_row02_traceSegment_098_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_098 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3240 108 108, g32p_row02_traceSegment_098_3240_0108, g32p_row02_traceSegment_098_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_098_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_098 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 3024 216 216, g32p_row02_traceSegment_098_3024_0216, g32p_row02_traceSegment_098_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_098_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_098 2592 864 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 2592 432 432, g32p_row02_traceSegment_098_2592_0432, g32p_row02_traceSegment_098_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_098_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_098 1728 1728 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 1728 864 864, g32p_row02_traceSegment_098_1728_0864, g32p_row02_traceSegment_098_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_098_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_098 0 3456 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_098 0 1728 1728, g32p_row02_traceSegment_098_0000_1728, g32p_row02_traceSegment_098_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 98 = [8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_098_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_099_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 0 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 0 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 0 13 14, g32p_row02_traceSegment_099_0000_0013, g32p_row02_traceSegment_099_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 27 13 14, g32p_row02_traceSegment_099_0027_0013, g32p_row02_traceSegment_099_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 0 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 0 27 27, g32p_row02_traceSegment_099_0000_0027, g32p_row02_traceSegment_099_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 54 13 14, g32p_row02_traceSegment_099_0054_0013, g32p_row02_traceSegment_099_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 81 13 14, g32p_row02_traceSegment_099_0081_0013, g32p_row02_traceSegment_099_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 54 27 27, g32p_row02_traceSegment_099_0054_0027, g32p_row02_traceSegment_099_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 0 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 0 54 54, g32p_row02_traceSegment_099_0000_0054, g32p_row02_traceSegment_099_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 108 13 14, g32p_row02_traceSegment_099_0108_0013, g32p_row02_traceSegment_099_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 135 13 14, g32p_row02_traceSegment_099_0135_0013, g32p_row02_traceSegment_099_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 108 27 27, g32p_row02_traceSegment_099_0108_0027, g32p_row02_traceSegment_099_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 162 13 14, g32p_row02_traceSegment_099_0162_0013, g32p_row02_traceSegment_099_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 189 13 14, g32p_row02_traceSegment_099_0189_0013, g32p_row02_traceSegment_099_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 162 27 27, g32p_row02_traceSegment_099_0162_0027, g32p_row02_traceSegment_099_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 108 54 54, g32p_row02_traceSegment_099_0108_0054, g32p_row02_traceSegment_099_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 0 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 0 108 108, g32p_row02_traceSegment_099_0000_0108, g32p_row02_traceSegment_099_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 216 13 14, g32p_row02_traceSegment_099_0216_0013, g32p_row02_traceSegment_099_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 243 13 14, g32p_row02_traceSegment_099_0243_0013, g32p_row02_traceSegment_099_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 216 27 27, g32p_row02_traceSegment_099_0216_0027, g32p_row02_traceSegment_099_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 270 13 14, g32p_row02_traceSegment_099_0270_0013, g32p_row02_traceSegment_099_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 297 13 14, g32p_row02_traceSegment_099_0297_0013, g32p_row02_traceSegment_099_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 270 27 27, g32p_row02_traceSegment_099_0270_0027, g32p_row02_traceSegment_099_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 216 54 54, g32p_row02_traceSegment_099_0216_0054, g32p_row02_traceSegment_099_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 324 13 14, g32p_row02_traceSegment_099_0324_0013, g32p_row02_traceSegment_099_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 351 13 14, g32p_row02_traceSegment_099_0351_0013, g32p_row02_traceSegment_099_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 324 27 27, g32p_row02_traceSegment_099_0324_0027, g32p_row02_traceSegment_099_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 378 13 14, g32p_row02_traceSegment_099_0378_0013, g32p_row02_traceSegment_099_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 405 13 14, g32p_row02_traceSegment_099_0405_0013, g32p_row02_traceSegment_099_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 378 27 27, g32p_row02_traceSegment_099_0378_0027, g32p_row02_traceSegment_099_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 324 54 54, g32p_row02_traceSegment_099_0324_0054, g32p_row02_traceSegment_099_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 216 108 108, g32p_row02_traceSegment_099_0216_0108, g32p_row02_traceSegment_099_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_099 0 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 0 216 216, g32p_row02_traceSegment_099_0000_0216, g32p_row02_traceSegment_099_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 432 13 14, g32p_row02_traceSegment_099_0432_0013, g32p_row02_traceSegment_099_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 459 13 14, g32p_row02_traceSegment_099_0459_0013, g32p_row02_traceSegment_099_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 432 27 27, g32p_row02_traceSegment_099_0432_0027, g32p_row02_traceSegment_099_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 486 13 14, g32p_row02_traceSegment_099_0486_0013, g32p_row02_traceSegment_099_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 513 13 14, g32p_row02_traceSegment_099_0513_0013, g32p_row02_traceSegment_099_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 486 27 27, g32p_row02_traceSegment_099_0486_0027, g32p_row02_traceSegment_099_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 432 54 54, g32p_row02_traceSegment_099_0432_0054, g32p_row02_traceSegment_099_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 540 13 14, g32p_row02_traceSegment_099_0540_0013, g32p_row02_traceSegment_099_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 567 13 14, g32p_row02_traceSegment_099_0567_0013, g32p_row02_traceSegment_099_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 540 27 27, g32p_row02_traceSegment_099_0540_0027, g32p_row02_traceSegment_099_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 594 13 14, g32p_row02_traceSegment_099_0594_0013, g32p_row02_traceSegment_099_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 621 13 14, g32p_row02_traceSegment_099_0621_0013, g32p_row02_traceSegment_099_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 594 27 27, g32p_row02_traceSegment_099_0594_0027, g32p_row02_traceSegment_099_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 540 54 54, g32p_row02_traceSegment_099_0540_0054, g32p_row02_traceSegment_099_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 432 108 108, g32p_row02_traceSegment_099_0432_0108, g32p_row02_traceSegment_099_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 648 13 14, g32p_row02_traceSegment_099_0648_0013, g32p_row02_traceSegment_099_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 675 13 14, g32p_row02_traceSegment_099_0675_0013, g32p_row02_traceSegment_099_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 648 27 27, g32p_row02_traceSegment_099_0648_0027, g32p_row02_traceSegment_099_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 702 13 14, g32p_row02_traceSegment_099_0702_0013, g32p_row02_traceSegment_099_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 729 13 14, g32p_row02_traceSegment_099_0729_0013, g32p_row02_traceSegment_099_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 702 27 27, g32p_row02_traceSegment_099_0702_0027, g32p_row02_traceSegment_099_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 648 54 54, g32p_row02_traceSegment_099_0648_0054, g32p_row02_traceSegment_099_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 756 13 14, g32p_row02_traceSegment_099_0756_0013, g32p_row02_traceSegment_099_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 783 13 14, g32p_row02_traceSegment_099_0783_0013, g32p_row02_traceSegment_099_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 756 27 27, g32p_row02_traceSegment_099_0756_0027, g32p_row02_traceSegment_099_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 810 13 14, g32p_row02_traceSegment_099_0810_0013, g32p_row02_traceSegment_099_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 837 13 14, g32p_row02_traceSegment_099_0837_0013, g32p_row02_traceSegment_099_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 810 27 27, g32p_row02_traceSegment_099_0810_0027, g32p_row02_traceSegment_099_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 756 54 54, g32p_row02_traceSegment_099_0756_0054, g32p_row02_traceSegment_099_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 648 108 108, g32p_row02_traceSegment_099_0648_0108, g32p_row02_traceSegment_099_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_099 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 432 216 216, g32p_row02_traceSegment_099_0432_0216, g32p_row02_traceSegment_099_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_099 0 864 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 0 432 432, g32p_row02_traceSegment_099_0000_0432, g32p_row02_traceSegment_099_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 864 13 14, g32p_row02_traceSegment_099_0864_0013, g32p_row02_traceSegment_099_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 891 13 14, g32p_row02_traceSegment_099_0891_0013, g32p_row02_traceSegment_099_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 864 27 27, g32p_row02_traceSegment_099_0864_0027, g32p_row02_traceSegment_099_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 918 13 14, g32p_row02_traceSegment_099_0918_0013, g32p_row02_traceSegment_099_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 945 13 14, g32p_row02_traceSegment_099_0945_0013, g32p_row02_traceSegment_099_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 918 27 27, g32p_row02_traceSegment_099_0918_0027, g32p_row02_traceSegment_099_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 864 54 54, g32p_row02_traceSegment_099_0864_0054, g32p_row02_traceSegment_099_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 972 13 14, g32p_row02_traceSegment_099_0972_0013, g32p_row02_traceSegment_099_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 999 13 14, g32p_row02_traceSegment_099_0999_0013, g32p_row02_traceSegment_099_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 972 27 27, g32p_row02_traceSegment_099_0972_0027, g32p_row02_traceSegment_099_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1026 13 14, g32p_row02_traceSegment_099_1026_0013, g32p_row02_traceSegment_099_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1053 13 14, g32p_row02_traceSegment_099_1053_0013, g32p_row02_traceSegment_099_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1026 27 27, g32p_row02_traceSegment_099_1026_0027, g32p_row02_traceSegment_099_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 972 54 54, g32p_row02_traceSegment_099_0972_0054, g32p_row02_traceSegment_099_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 864 108 108, g32p_row02_traceSegment_099_0864_0108, g32p_row02_traceSegment_099_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1080 13 14, g32p_row02_traceSegment_099_1080_0013, g32p_row02_traceSegment_099_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1107 13 14, g32p_row02_traceSegment_099_1107_0013, g32p_row02_traceSegment_099_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1080 27 27, g32p_row02_traceSegment_099_1080_0027, g32p_row02_traceSegment_099_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1134 13 14, g32p_row02_traceSegment_099_1134_0013, g32p_row02_traceSegment_099_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1161 13 14, g32p_row02_traceSegment_099_1161_0013, g32p_row02_traceSegment_099_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1134 27 27, g32p_row02_traceSegment_099_1134_0027, g32p_row02_traceSegment_099_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1080 54 54, g32p_row02_traceSegment_099_1080_0054, g32p_row02_traceSegment_099_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1188 13 14, g32p_row02_traceSegment_099_1188_0013, g32p_row02_traceSegment_099_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1215 13 14, g32p_row02_traceSegment_099_1215_0013, g32p_row02_traceSegment_099_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1188 27 27, g32p_row02_traceSegment_099_1188_0027, g32p_row02_traceSegment_099_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1242 13 14, g32p_row02_traceSegment_099_1242_0013, g32p_row02_traceSegment_099_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1269 13 14, g32p_row02_traceSegment_099_1269_0013, g32p_row02_traceSegment_099_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1242 27 27, g32p_row02_traceSegment_099_1242_0027, g32p_row02_traceSegment_099_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1188 54 54, g32p_row02_traceSegment_099_1188_0054, g32p_row02_traceSegment_099_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1080 108 108, g32p_row02_traceSegment_099_1080_0108, g32p_row02_traceSegment_099_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_099 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 864 216 216, g32p_row02_traceSegment_099_0864_0216, g32p_row02_traceSegment_099_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1296 13 14, g32p_row02_traceSegment_099_1296_0013, g32p_row02_traceSegment_099_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1323 13 14, g32p_row02_traceSegment_099_1323_0013, g32p_row02_traceSegment_099_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1296 27 27, g32p_row02_traceSegment_099_1296_0027, g32p_row02_traceSegment_099_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1350 13 14, g32p_row02_traceSegment_099_1350_0013, g32p_row02_traceSegment_099_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1377 13 14, g32p_row02_traceSegment_099_1377_0013, g32p_row02_traceSegment_099_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1350 27 27, g32p_row02_traceSegment_099_1350_0027, g32p_row02_traceSegment_099_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1296 54 54, g32p_row02_traceSegment_099_1296_0054, g32p_row02_traceSegment_099_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1404 13 14, g32p_row02_traceSegment_099_1404_0013, g32p_row02_traceSegment_099_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1431 13 14, g32p_row02_traceSegment_099_1431_0013, g32p_row02_traceSegment_099_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1404 27 27, g32p_row02_traceSegment_099_1404_0027, g32p_row02_traceSegment_099_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1458 13 14, g32p_row02_traceSegment_099_1458_0013, g32p_row02_traceSegment_099_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1485 13 14, g32p_row02_traceSegment_099_1485_0013, g32p_row02_traceSegment_099_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1458 27 27, g32p_row02_traceSegment_099_1458_0027, g32p_row02_traceSegment_099_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1404 54 54, g32p_row02_traceSegment_099_1404_0054, g32p_row02_traceSegment_099_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1296 108 108, g32p_row02_traceSegment_099_1296_0108, g32p_row02_traceSegment_099_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1512 13 14, g32p_row02_traceSegment_099_1512_0013, g32p_row02_traceSegment_099_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1539 13 14, g32p_row02_traceSegment_099_1539_0013, g32p_row02_traceSegment_099_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1512 27 27, g32p_row02_traceSegment_099_1512_0027, g32p_row02_traceSegment_099_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1566 13 14, g32p_row02_traceSegment_099_1566_0013, g32p_row02_traceSegment_099_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1593 13 14, g32p_row02_traceSegment_099_1593_0013, g32p_row02_traceSegment_099_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1566 27 27, g32p_row02_traceSegment_099_1566_0027, g32p_row02_traceSegment_099_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1512 54 54, g32p_row02_traceSegment_099_1512_0054, g32p_row02_traceSegment_099_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1620 13 14, g32p_row02_traceSegment_099_1620_0013, g32p_row02_traceSegment_099_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1647 13 14, g32p_row02_traceSegment_099_1647_0013, g32p_row02_traceSegment_099_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1620 27 27, g32p_row02_traceSegment_099_1620_0027, g32p_row02_traceSegment_099_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1674 13 14, g32p_row02_traceSegment_099_1674_0013, g32p_row02_traceSegment_099_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1701 13 14, g32p_row02_traceSegment_099_1701_0013, g32p_row02_traceSegment_099_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1674 27 27, g32p_row02_traceSegment_099_1674_0027, g32p_row02_traceSegment_099_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1620 54 54, g32p_row02_traceSegment_099_1620_0054, g32p_row02_traceSegment_099_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1512 108 108, g32p_row02_traceSegment_099_1512_0108, g32p_row02_traceSegment_099_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_099 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1296 216 216, g32p_row02_traceSegment_099_1296_0216, g32p_row02_traceSegment_099_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_099 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 864 432 432, g32p_row02_traceSegment_099_0864_0432, g32p_row02_traceSegment_099_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_099 0 1728 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 0 864 864, g32p_row02_traceSegment_099_0000_0864, g32p_row02_traceSegment_099_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1728 13 14, g32p_row02_traceSegment_099_1728_0013, g32p_row02_traceSegment_099_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1755 13 14, g32p_row02_traceSegment_099_1755_0013, g32p_row02_traceSegment_099_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1728 27 27, g32p_row02_traceSegment_099_1728_0027, g32p_row02_traceSegment_099_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1782 13 14, g32p_row02_traceSegment_099_1782_0013, g32p_row02_traceSegment_099_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1809 13 14, g32p_row02_traceSegment_099_1809_0013, g32p_row02_traceSegment_099_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1782 27 27, g32p_row02_traceSegment_099_1782_0027, g32p_row02_traceSegment_099_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1728 54 54, g32p_row02_traceSegment_099_1728_0054, g32p_row02_traceSegment_099_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1836 13 14, g32p_row02_traceSegment_099_1836_0013, g32p_row02_traceSegment_099_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1863 13 14, g32p_row02_traceSegment_099_1863_0013, g32p_row02_traceSegment_099_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1836 27 27, g32p_row02_traceSegment_099_1836_0027, g32p_row02_traceSegment_099_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1890 13 14, g32p_row02_traceSegment_099_1890_0013, g32p_row02_traceSegment_099_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1917 13 14, g32p_row02_traceSegment_099_1917_0013, g32p_row02_traceSegment_099_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1890 27 27, g32p_row02_traceSegment_099_1890_0027, g32p_row02_traceSegment_099_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1836 54 54, g32p_row02_traceSegment_099_1836_0054, g32p_row02_traceSegment_099_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1728 108 108, g32p_row02_traceSegment_099_1728_0108, g32p_row02_traceSegment_099_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1944 13 14, g32p_row02_traceSegment_099_1944_0013, g32p_row02_traceSegment_099_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1971 13 14, g32p_row02_traceSegment_099_1971_0013, g32p_row02_traceSegment_099_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1944 27 27, g32p_row02_traceSegment_099_1944_0027, g32p_row02_traceSegment_099_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1998 13 14, g32p_row02_traceSegment_099_1998_0013, g32p_row02_traceSegment_099_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2025 13 14, g32p_row02_traceSegment_099_2025_0013, g32p_row02_traceSegment_099_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1998 27 27, g32p_row02_traceSegment_099_1998_0027, g32p_row02_traceSegment_099_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1944 54 54, g32p_row02_traceSegment_099_1944_0054, g32p_row02_traceSegment_099_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2052 13 14, g32p_row02_traceSegment_099_2052_0013, g32p_row02_traceSegment_099_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2079 13 14, g32p_row02_traceSegment_099_2079_0013, g32p_row02_traceSegment_099_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2052 27 27, g32p_row02_traceSegment_099_2052_0027, g32p_row02_traceSegment_099_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2106 13 14, g32p_row02_traceSegment_099_2106_0013, g32p_row02_traceSegment_099_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2133 13 14, g32p_row02_traceSegment_099_2133_0013, g32p_row02_traceSegment_099_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2106 27 27, g32p_row02_traceSegment_099_2106_0027, g32p_row02_traceSegment_099_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2052 54 54, g32p_row02_traceSegment_099_2052_0054, g32p_row02_traceSegment_099_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1944 108 108, g32p_row02_traceSegment_099_1944_0108, g32p_row02_traceSegment_099_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_099 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1728 216 216, g32p_row02_traceSegment_099_1728_0216, g32p_row02_traceSegment_099_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2160 13 14, g32p_row02_traceSegment_099_2160_0013, g32p_row02_traceSegment_099_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2187 13 14, g32p_row02_traceSegment_099_2187_0013, g32p_row02_traceSegment_099_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2160 27 27, g32p_row02_traceSegment_099_2160_0027, g32p_row02_traceSegment_099_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2214 13 14, g32p_row02_traceSegment_099_2214_0013, g32p_row02_traceSegment_099_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2241 13 14, g32p_row02_traceSegment_099_2241_0013, g32p_row02_traceSegment_099_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2214 27 27, g32p_row02_traceSegment_099_2214_0027, g32p_row02_traceSegment_099_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2160 54 54, g32p_row02_traceSegment_099_2160_0054, g32p_row02_traceSegment_099_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2268 13 14, g32p_row02_traceSegment_099_2268_0013, g32p_row02_traceSegment_099_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2295 13 14, g32p_row02_traceSegment_099_2295_0013, g32p_row02_traceSegment_099_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2268 27 27, g32p_row02_traceSegment_099_2268_0027, g32p_row02_traceSegment_099_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2322 13 14, g32p_row02_traceSegment_099_2322_0013, g32p_row02_traceSegment_099_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2349 13 14, g32p_row02_traceSegment_099_2349_0013, g32p_row02_traceSegment_099_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2322 27 27, g32p_row02_traceSegment_099_2322_0027, g32p_row02_traceSegment_099_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2268 54 54, g32p_row02_traceSegment_099_2268_0054, g32p_row02_traceSegment_099_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2160 108 108, g32p_row02_traceSegment_099_2160_0108, g32p_row02_traceSegment_099_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2376 13 14, g32p_row02_traceSegment_099_2376_0013, g32p_row02_traceSegment_099_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2403 13 14, g32p_row02_traceSegment_099_2403_0013, g32p_row02_traceSegment_099_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2376 27 27, g32p_row02_traceSegment_099_2376_0027, g32p_row02_traceSegment_099_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2430 13 14, g32p_row02_traceSegment_099_2430_0013, g32p_row02_traceSegment_099_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2457 13 14, g32p_row02_traceSegment_099_2457_0013, g32p_row02_traceSegment_099_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2430 27 27, g32p_row02_traceSegment_099_2430_0027, g32p_row02_traceSegment_099_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2376 54 54, g32p_row02_traceSegment_099_2376_0054, g32p_row02_traceSegment_099_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2484 13 14, g32p_row02_traceSegment_099_2484_0013, g32p_row02_traceSegment_099_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2511 13 14, g32p_row02_traceSegment_099_2511_0013, g32p_row02_traceSegment_099_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2484 27 27, g32p_row02_traceSegment_099_2484_0027, g32p_row02_traceSegment_099_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2538 13 14, g32p_row02_traceSegment_099_2538_0013, g32p_row02_traceSegment_099_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2565 13 14, g32p_row02_traceSegment_099_2565_0013, g32p_row02_traceSegment_099_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2538 27 27, g32p_row02_traceSegment_099_2538_0027, g32p_row02_traceSegment_099_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2484 54 54, g32p_row02_traceSegment_099_2484_0054, g32p_row02_traceSegment_099_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2376 108 108, g32p_row02_traceSegment_099_2376_0108, g32p_row02_traceSegment_099_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_099 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2160 216 216, g32p_row02_traceSegment_099_2160_0216, g32p_row02_traceSegment_099_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_099 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1728 432 432, g32p_row02_traceSegment_099_1728_0432, g32p_row02_traceSegment_099_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2592 13 14, g32p_row02_traceSegment_099_2592_0013, g32p_row02_traceSegment_099_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2619 13 14, g32p_row02_traceSegment_099_2619_0013, g32p_row02_traceSegment_099_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2592 27 27, g32p_row02_traceSegment_099_2592_0027, g32p_row02_traceSegment_099_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2646 13 14, g32p_row02_traceSegment_099_2646_0013, g32p_row02_traceSegment_099_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2673 13 14, g32p_row02_traceSegment_099_2673_0013, g32p_row02_traceSegment_099_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2646 27 27, g32p_row02_traceSegment_099_2646_0027, g32p_row02_traceSegment_099_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2592 54 54, g32p_row02_traceSegment_099_2592_0054, g32p_row02_traceSegment_099_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2700 13 14, g32p_row02_traceSegment_099_2700_0013, g32p_row02_traceSegment_099_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2727 13 14, g32p_row02_traceSegment_099_2727_0013, g32p_row02_traceSegment_099_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2700 27 27, g32p_row02_traceSegment_099_2700_0027, g32p_row02_traceSegment_099_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2754 13 14, g32p_row02_traceSegment_099_2754_0013, g32p_row02_traceSegment_099_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2781 13 14, g32p_row02_traceSegment_099_2781_0013, g32p_row02_traceSegment_099_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2754 27 27, g32p_row02_traceSegment_099_2754_0027, g32p_row02_traceSegment_099_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2700 54 54, g32p_row02_traceSegment_099_2700_0054, g32p_row02_traceSegment_099_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2592 108 108, g32p_row02_traceSegment_099_2592_0108, g32p_row02_traceSegment_099_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2808 13 14, g32p_row02_traceSegment_099_2808_0013, g32p_row02_traceSegment_099_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2835 13 14, g32p_row02_traceSegment_099_2835_0013, g32p_row02_traceSegment_099_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2808 27 27, g32p_row02_traceSegment_099_2808_0027, g32p_row02_traceSegment_099_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2862 13 14, g32p_row02_traceSegment_099_2862_0013, g32p_row02_traceSegment_099_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2889 13 14, g32p_row02_traceSegment_099_2889_0013, g32p_row02_traceSegment_099_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2862 27 27, g32p_row02_traceSegment_099_2862_0027, g32p_row02_traceSegment_099_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2808 54 54, g32p_row02_traceSegment_099_2808_0054, g32p_row02_traceSegment_099_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2916 13 14, g32p_row02_traceSegment_099_2916_0013, g32p_row02_traceSegment_099_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2943 13 14, g32p_row02_traceSegment_099_2943_0013, g32p_row02_traceSegment_099_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2916 27 27, g32p_row02_traceSegment_099_2916_0027, g32p_row02_traceSegment_099_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2970 13 14, g32p_row02_traceSegment_099_2970_0013, g32p_row02_traceSegment_099_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2997 13 14, g32p_row02_traceSegment_099_2997_0013, g32p_row02_traceSegment_099_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2970 27 27, g32p_row02_traceSegment_099_2970_0027, g32p_row02_traceSegment_099_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2916 54 54, g32p_row02_traceSegment_099_2916_0054, g32p_row02_traceSegment_099_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2808 108 108, g32p_row02_traceSegment_099_2808_0108, g32p_row02_traceSegment_099_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_099 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2592 216 216, g32p_row02_traceSegment_099_2592_0216, g32p_row02_traceSegment_099_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3024 13 14, g32p_row02_traceSegment_099_3024_0013, g32p_row02_traceSegment_099_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3051 13 14, g32p_row02_traceSegment_099_3051_0013, g32p_row02_traceSegment_099_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3024 27 27, g32p_row02_traceSegment_099_3024_0027, g32p_row02_traceSegment_099_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3078 13 14, g32p_row02_traceSegment_099_3078_0013, g32p_row02_traceSegment_099_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3105 13 14, g32p_row02_traceSegment_099_3105_0013, g32p_row02_traceSegment_099_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3078 27 27, g32p_row02_traceSegment_099_3078_0027, g32p_row02_traceSegment_099_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3024 54 54, g32p_row02_traceSegment_099_3024_0054, g32p_row02_traceSegment_099_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3132 13 14, g32p_row02_traceSegment_099_3132_0013, g32p_row02_traceSegment_099_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3159 13 14, g32p_row02_traceSegment_099_3159_0013, g32p_row02_traceSegment_099_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3132 27 27, g32p_row02_traceSegment_099_3132_0027, g32p_row02_traceSegment_099_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3186 13 14, g32p_row02_traceSegment_099_3186_0013, g32p_row02_traceSegment_099_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3213 13 14, g32p_row02_traceSegment_099_3213_0013, g32p_row02_traceSegment_099_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3186 27 27, g32p_row02_traceSegment_099_3186_0027, g32p_row02_traceSegment_099_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3132 54 54, g32p_row02_traceSegment_099_3132_0054, g32p_row02_traceSegment_099_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3024 108 108, g32p_row02_traceSegment_099_3024_0108, g32p_row02_traceSegment_099_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3240 13 14, g32p_row02_traceSegment_099_3240_0013, g32p_row02_traceSegment_099_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3267 13 14, g32p_row02_traceSegment_099_3267_0013, g32p_row02_traceSegment_099_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3240 27 27, g32p_row02_traceSegment_099_3240_0027, g32p_row02_traceSegment_099_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3294 13 14, g32p_row02_traceSegment_099_3294_0013, g32p_row02_traceSegment_099_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3321 13 14, g32p_row02_traceSegment_099_3321_0013, g32p_row02_traceSegment_099_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3294 27 27, g32p_row02_traceSegment_099_3294_0027, g32p_row02_traceSegment_099_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3240 54 54, g32p_row02_traceSegment_099_3240_0054, g32p_row02_traceSegment_099_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3348 13 14, g32p_row02_traceSegment_099_3348_0013, g32p_row02_traceSegment_099_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3375 13 14, g32p_row02_traceSegment_099_3375_0013, g32p_row02_traceSegment_099_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3348 27 27, g32p_row02_traceSegment_099_3348_0027, g32p_row02_traceSegment_099_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3402 13 14, g32p_row02_traceSegment_099_3402_0013, g32p_row02_traceSegment_099_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_099 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_099 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_099_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_099 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3429 13 14, g32p_row02_traceSegment_099_3429_0013, g32p_row02_traceSegment_099_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_099 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3402 27 27, g32p_row02_traceSegment_099_3402_0027, g32p_row02_traceSegment_099_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_099 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3348 54 54, g32p_row02_traceSegment_099_3348_0054, g32p_row02_traceSegment_099_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_099 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3240 108 108, g32p_row02_traceSegment_099_3240_0108, g32p_row02_traceSegment_099_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_099_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_099 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 3024 216 216, g32p_row02_traceSegment_099_3024_0216, g32p_row02_traceSegment_099_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_099_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_099 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 2592 432 432, g32p_row02_traceSegment_099_2592_0432, g32p_row02_traceSegment_099_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_099_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_099 1728 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 1728 864 864, g32p_row02_traceSegment_099_1728_0864, g32p_row02_traceSegment_099_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_099_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_099 0 3456 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_099 0 1728 1728, g32p_row02_traceSegment_099_0000_1728, g32p_row02_traceSegment_099_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_099_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_100 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 100 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_100_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 0 13 14, g32p_row02_traceSegment_100_0000_0013, g32p_row02_traceSegment_100_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 27 13 14, g32p_row02_traceSegment_100_0027_0013, g32p_row02_traceSegment_100_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 0 27 27, g32p_row02_traceSegment_100_0000_0027, g32p_row02_traceSegment_100_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 54 13 14, g32p_row02_traceSegment_100_0054_0013, g32p_row02_traceSegment_100_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 81 13 14, g32p_row02_traceSegment_100_0081_0013, g32p_row02_traceSegment_100_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 54 27 27, g32p_row02_traceSegment_100_0054_0027, g32p_row02_traceSegment_100_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 0 54 54, g32p_row02_traceSegment_100_0000_0054, g32p_row02_traceSegment_100_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 108 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 121 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 108 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 108 13 14, g32p_row02_traceSegment_100_0108_0013, g32p_row02_traceSegment_100_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 135 13 14, g32p_row02_traceSegment_100_0135_0013, g32p_row02_traceSegment_100_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 108 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 108 27 27, g32p_row02_traceSegment_100_0108_0027, g32p_row02_traceSegment_100_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 162 13 14, g32p_row02_traceSegment_100_0162_0013, g32p_row02_traceSegment_100_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 189 13 14, g32p_row02_traceSegment_100_0189_0013, g32p_row02_traceSegment_100_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 162 27 27, g32p_row02_traceSegment_100_0162_0027, g32p_row02_traceSegment_100_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 108 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 108 54 54, g32p_row02_traceSegment_100_0108_0054, g32p_row02_traceSegment_100_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 0 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 0 108 108, g32p_row02_traceSegment_100_0000_0108, g32p_row02_traceSegment_100_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 216 13 14, g32p_row02_traceSegment_100_0216_0013, g32p_row02_traceSegment_100_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 243 13 14, g32p_row02_traceSegment_100_0243_0013, g32p_row02_traceSegment_100_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 216 27 27, g32p_row02_traceSegment_100_0216_0027, g32p_row02_traceSegment_100_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 270 13 14, g32p_row02_traceSegment_100_0270_0013, g32p_row02_traceSegment_100_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 297 13 14, g32p_row02_traceSegment_100_0297_0013, g32p_row02_traceSegment_100_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 270 27 27, g32p_row02_traceSegment_100_0270_0027, g32p_row02_traceSegment_100_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 216 54 54, g32p_row02_traceSegment_100_0216_0054, g32p_row02_traceSegment_100_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 324 13 14, g32p_row02_traceSegment_100_0324_0013, g32p_row02_traceSegment_100_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 351 13 14, g32p_row02_traceSegment_100_0351_0013, g32p_row02_traceSegment_100_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 324 27 27, g32p_row02_traceSegment_100_0324_0027, g32p_row02_traceSegment_100_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 378 13 14, g32p_row02_traceSegment_100_0378_0013, g32p_row02_traceSegment_100_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 405 13 14, g32p_row02_traceSegment_100_0405_0013, g32p_row02_traceSegment_100_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 378 27 27, g32p_row02_traceSegment_100_0378_0027, g32p_row02_traceSegment_100_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 324 54 54, g32p_row02_traceSegment_100_0324_0054, g32p_row02_traceSegment_100_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 216 108 108, g32p_row02_traceSegment_100_0216_0108, g32p_row02_traceSegment_100_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_100 0 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 0 216 216, g32p_row02_traceSegment_100_0000_0216, g32p_row02_traceSegment_100_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 432 13 14, g32p_row02_traceSegment_100_0432_0013, g32p_row02_traceSegment_100_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 459 13 14, g32p_row02_traceSegment_100_0459_0013, g32p_row02_traceSegment_100_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 432 27 27, g32p_row02_traceSegment_100_0432_0027, g32p_row02_traceSegment_100_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 486 13 14, g32p_row02_traceSegment_100_0486_0013, g32p_row02_traceSegment_100_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 513 13 14, g32p_row02_traceSegment_100_0513_0013, g32p_row02_traceSegment_100_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 486 27 27, g32p_row02_traceSegment_100_0486_0027, g32p_row02_traceSegment_100_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 432 54 54, g32p_row02_traceSegment_100_0432_0054, g32p_row02_traceSegment_100_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 540 13 14, g32p_row02_traceSegment_100_0540_0013, g32p_row02_traceSegment_100_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 567 13 14, g32p_row02_traceSegment_100_0567_0013, g32p_row02_traceSegment_100_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 540 27 27, g32p_row02_traceSegment_100_0540_0027, g32p_row02_traceSegment_100_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 594 13 14, g32p_row02_traceSegment_100_0594_0013, g32p_row02_traceSegment_100_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 621 13 14, g32p_row02_traceSegment_100_0621_0013, g32p_row02_traceSegment_100_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 594 27 27, g32p_row02_traceSegment_100_0594_0027, g32p_row02_traceSegment_100_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 540 54 54, g32p_row02_traceSegment_100_0540_0054, g32p_row02_traceSegment_100_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 432 108 108, g32p_row02_traceSegment_100_0432_0108, g32p_row02_traceSegment_100_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 648 13 14, g32p_row02_traceSegment_100_0648_0013, g32p_row02_traceSegment_100_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 675 13 14, g32p_row02_traceSegment_100_0675_0013, g32p_row02_traceSegment_100_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 648 27 27, g32p_row02_traceSegment_100_0648_0027, g32p_row02_traceSegment_100_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 702 13 14, g32p_row02_traceSegment_100_0702_0013, g32p_row02_traceSegment_100_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 729 13 14, g32p_row02_traceSegment_100_0729_0013, g32p_row02_traceSegment_100_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 702 27 27, g32p_row02_traceSegment_100_0702_0027, g32p_row02_traceSegment_100_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 648 54 54, g32p_row02_traceSegment_100_0648_0054, g32p_row02_traceSegment_100_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 756 13 14, g32p_row02_traceSegment_100_0756_0013, g32p_row02_traceSegment_100_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 783 13 14, g32p_row02_traceSegment_100_0783_0013, g32p_row02_traceSegment_100_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 756 27 27, g32p_row02_traceSegment_100_0756_0027, g32p_row02_traceSegment_100_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 810 13 14, g32p_row02_traceSegment_100_0810_0013, g32p_row02_traceSegment_100_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 837 13 14, g32p_row02_traceSegment_100_0837_0013, g32p_row02_traceSegment_100_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 810 27 27, g32p_row02_traceSegment_100_0810_0027, g32p_row02_traceSegment_100_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 756 54 54, g32p_row02_traceSegment_100_0756_0054, g32p_row02_traceSegment_100_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 648 108 108, g32p_row02_traceSegment_100_0648_0108, g32p_row02_traceSegment_100_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_100 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 432 216 216, g32p_row02_traceSegment_100_0432_0216, g32p_row02_traceSegment_100_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_100 0 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 0 432 432, g32p_row02_traceSegment_100_0000_0432, g32p_row02_traceSegment_100_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 864 13 14, g32p_row02_traceSegment_100_0864_0013, g32p_row02_traceSegment_100_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 891 13 14, g32p_row02_traceSegment_100_0891_0013, g32p_row02_traceSegment_100_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 864 27 27, g32p_row02_traceSegment_100_0864_0027, g32p_row02_traceSegment_100_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 918 13 14, g32p_row02_traceSegment_100_0918_0013, g32p_row02_traceSegment_100_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 945 13 14, g32p_row02_traceSegment_100_0945_0013, g32p_row02_traceSegment_100_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 918 27 27, g32p_row02_traceSegment_100_0918_0027, g32p_row02_traceSegment_100_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 864 54 54, g32p_row02_traceSegment_100_0864_0054, g32p_row02_traceSegment_100_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 972 13 14, g32p_row02_traceSegment_100_0972_0013, g32p_row02_traceSegment_100_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 999 13 14, g32p_row02_traceSegment_100_0999_0013, g32p_row02_traceSegment_100_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 972 27 27, g32p_row02_traceSegment_100_0972_0027, g32p_row02_traceSegment_100_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1026 13 14, g32p_row02_traceSegment_100_1026_0013, g32p_row02_traceSegment_100_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1053 13 14, g32p_row02_traceSegment_100_1053_0013, g32p_row02_traceSegment_100_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1026 27 27, g32p_row02_traceSegment_100_1026_0027, g32p_row02_traceSegment_100_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 972 54 54, g32p_row02_traceSegment_100_0972_0054, g32p_row02_traceSegment_100_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 864 108 108, g32p_row02_traceSegment_100_0864_0108, g32p_row02_traceSegment_100_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1080 13 14, g32p_row02_traceSegment_100_1080_0013, g32p_row02_traceSegment_100_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1107 13 14, g32p_row02_traceSegment_100_1107_0013, g32p_row02_traceSegment_100_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1080 27 27, g32p_row02_traceSegment_100_1080_0027, g32p_row02_traceSegment_100_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1134 13 14, g32p_row02_traceSegment_100_1134_0013, g32p_row02_traceSegment_100_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1161 13 14, g32p_row02_traceSegment_100_1161_0013, g32p_row02_traceSegment_100_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1134 27 27, g32p_row02_traceSegment_100_1134_0027, g32p_row02_traceSegment_100_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1080 54 54, g32p_row02_traceSegment_100_1080_0054, g32p_row02_traceSegment_100_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1188 13 14, g32p_row02_traceSegment_100_1188_0013, g32p_row02_traceSegment_100_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1215 13 14, g32p_row02_traceSegment_100_1215_0013, g32p_row02_traceSegment_100_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1188 27 27, g32p_row02_traceSegment_100_1188_0027, g32p_row02_traceSegment_100_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1242 13 14, g32p_row02_traceSegment_100_1242_0013, g32p_row02_traceSegment_100_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1269 13 14, g32p_row02_traceSegment_100_1269_0013, g32p_row02_traceSegment_100_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1242 27 27, g32p_row02_traceSegment_100_1242_0027, g32p_row02_traceSegment_100_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1188 54 54, g32p_row02_traceSegment_100_1188_0054, g32p_row02_traceSegment_100_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1080 108 108, g32p_row02_traceSegment_100_1080_0108, g32p_row02_traceSegment_100_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_100 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 864 216 216, g32p_row02_traceSegment_100_0864_0216, g32p_row02_traceSegment_100_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1296 13 14, g32p_row02_traceSegment_100_1296_0013, g32p_row02_traceSegment_100_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1323 13 14, g32p_row02_traceSegment_100_1323_0013, g32p_row02_traceSegment_100_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1296 27 27, g32p_row02_traceSegment_100_1296_0027, g32p_row02_traceSegment_100_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1350 13 14, g32p_row02_traceSegment_100_1350_0013, g32p_row02_traceSegment_100_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1377 13 14, g32p_row02_traceSegment_100_1377_0013, g32p_row02_traceSegment_100_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1350 27 27, g32p_row02_traceSegment_100_1350_0027, g32p_row02_traceSegment_100_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1296 54 54, g32p_row02_traceSegment_100_1296_0054, g32p_row02_traceSegment_100_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1404 13 14, g32p_row02_traceSegment_100_1404_0013, g32p_row02_traceSegment_100_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1431 13 14, g32p_row02_traceSegment_100_1431_0013, g32p_row02_traceSegment_100_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1404 27 27, g32p_row02_traceSegment_100_1404_0027, g32p_row02_traceSegment_100_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1458 13 14, g32p_row02_traceSegment_100_1458_0013, g32p_row02_traceSegment_100_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1485 13 14, g32p_row02_traceSegment_100_1485_0013, g32p_row02_traceSegment_100_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1458 27 27, g32p_row02_traceSegment_100_1458_0027, g32p_row02_traceSegment_100_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1404 54 54, g32p_row02_traceSegment_100_1404_0054, g32p_row02_traceSegment_100_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1296 108 108, g32p_row02_traceSegment_100_1296_0108, g32p_row02_traceSegment_100_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1512 13 14, g32p_row02_traceSegment_100_1512_0013, g32p_row02_traceSegment_100_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1552 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1539 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1539 13 14, g32p_row02_traceSegment_100_1539_0013, g32p_row02_traceSegment_100_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1512 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1512 27 27, g32p_row02_traceSegment_100_1512_0027, g32p_row02_traceSegment_100_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1566 13 14, g32p_row02_traceSegment_100_1566_0013, g32p_row02_traceSegment_100_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1593 13 14, g32p_row02_traceSegment_100_1593_0013, g32p_row02_traceSegment_100_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1566 27 27, g32p_row02_traceSegment_100_1566_0027, g32p_row02_traceSegment_100_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 1512 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1512 54 54, g32p_row02_traceSegment_100_1512_0054, g32p_row02_traceSegment_100_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1620 13 14, g32p_row02_traceSegment_100_1620_0013, g32p_row02_traceSegment_100_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1647 13 14, g32p_row02_traceSegment_100_1647_0013, g32p_row02_traceSegment_100_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1620 27 27, g32p_row02_traceSegment_100_1620_0027, g32p_row02_traceSegment_100_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1674 13 14, g32p_row02_traceSegment_100_1674_0013, g32p_row02_traceSegment_100_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1701 13 14, g32p_row02_traceSegment_100_1701_0013, g32p_row02_traceSegment_100_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1674 27 27, g32p_row02_traceSegment_100_1674_0027, g32p_row02_traceSegment_100_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1620 54 54, g32p_row02_traceSegment_100_1620_0054, g32p_row02_traceSegment_100_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 1512 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1512 108 108, g32p_row02_traceSegment_100_1512_0108, g32p_row02_traceSegment_100_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_100 1296 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1296 216 216, g32p_row02_traceSegment_100_1296_0216, g32p_row02_traceSegment_100_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_100 864 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 864 432 432, g32p_row02_traceSegment_100_0864_0432, g32p_row02_traceSegment_100_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_100 0 1728 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 0 864 864, g32p_row02_traceSegment_100_0000_0864, g32p_row02_traceSegment_100_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1728 13 14, g32p_row02_traceSegment_100_1728_0013, g32p_row02_traceSegment_100_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1755 13 14, g32p_row02_traceSegment_100_1755_0013, g32p_row02_traceSegment_100_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1728 27 27, g32p_row02_traceSegment_100_1728_0027, g32p_row02_traceSegment_100_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1782 13 14, g32p_row02_traceSegment_100_1782_0013, g32p_row02_traceSegment_100_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1809 13 14, g32p_row02_traceSegment_100_1809_0013, g32p_row02_traceSegment_100_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1782 27 27, g32p_row02_traceSegment_100_1782_0027, g32p_row02_traceSegment_100_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1728 54 54, g32p_row02_traceSegment_100_1728_0054, g32p_row02_traceSegment_100_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1836 13 14, g32p_row02_traceSegment_100_1836_0013, g32p_row02_traceSegment_100_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1863 13 14, g32p_row02_traceSegment_100_1863_0013, g32p_row02_traceSegment_100_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1836 27 27, g32p_row02_traceSegment_100_1836_0027, g32p_row02_traceSegment_100_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1890 13 14, g32p_row02_traceSegment_100_1890_0013, g32p_row02_traceSegment_100_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1917 13 14, g32p_row02_traceSegment_100_1917_0013, g32p_row02_traceSegment_100_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1890 27 27, g32p_row02_traceSegment_100_1890_0027, g32p_row02_traceSegment_100_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1836 54 54, g32p_row02_traceSegment_100_1836_0054, g32p_row02_traceSegment_100_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1728 108 108, g32p_row02_traceSegment_100_1728_0108, g32p_row02_traceSegment_100_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1944 13 14, g32p_row02_traceSegment_100_1944_0013, g32p_row02_traceSegment_100_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1971 13 14, g32p_row02_traceSegment_100_1971_0013, g32p_row02_traceSegment_100_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1944 27 27, g32p_row02_traceSegment_100_1944_0027, g32p_row02_traceSegment_100_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1998 13 14, g32p_row02_traceSegment_100_1998_0013, g32p_row02_traceSegment_100_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2025 13 14, g32p_row02_traceSegment_100_2025_0013, g32p_row02_traceSegment_100_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1998 27 27, g32p_row02_traceSegment_100_1998_0027, g32p_row02_traceSegment_100_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1944 54 54, g32p_row02_traceSegment_100_1944_0054, g32p_row02_traceSegment_100_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2052 13 14, g32p_row02_traceSegment_100_2052_0013, g32p_row02_traceSegment_100_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2079 13 14, g32p_row02_traceSegment_100_2079_0013, g32p_row02_traceSegment_100_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2052 27 27, g32p_row02_traceSegment_100_2052_0027, g32p_row02_traceSegment_100_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2106 13 14, g32p_row02_traceSegment_100_2106_0013, g32p_row02_traceSegment_100_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2133 13 14, g32p_row02_traceSegment_100_2133_0013, g32p_row02_traceSegment_100_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2106 27 27, g32p_row02_traceSegment_100_2106_0027, g32p_row02_traceSegment_100_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2052 54 54, g32p_row02_traceSegment_100_2052_0054, g32p_row02_traceSegment_100_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1944 108 108, g32p_row02_traceSegment_100_1944_0108, g32p_row02_traceSegment_100_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_100 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1728 216 216, g32p_row02_traceSegment_100_1728_0216, g32p_row02_traceSegment_100_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2160 13 14, g32p_row02_traceSegment_100_2160_0013, g32p_row02_traceSegment_100_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2187 13 14, g32p_row02_traceSegment_100_2187_0013, g32p_row02_traceSegment_100_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2160 27 27, g32p_row02_traceSegment_100_2160_0027, g32p_row02_traceSegment_100_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2214 13 14, g32p_row02_traceSegment_100_2214_0013, g32p_row02_traceSegment_100_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2241 13 14, g32p_row02_traceSegment_100_2241_0013, g32p_row02_traceSegment_100_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2214 27 27, g32p_row02_traceSegment_100_2214_0027, g32p_row02_traceSegment_100_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2160 54 54, g32p_row02_traceSegment_100_2160_0054, g32p_row02_traceSegment_100_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2268 13 14, g32p_row02_traceSegment_100_2268_0013, g32p_row02_traceSegment_100_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2295 13 14, g32p_row02_traceSegment_100_2295_0013, g32p_row02_traceSegment_100_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2268 27 27, g32p_row02_traceSegment_100_2268_0027, g32p_row02_traceSegment_100_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2322 13 14, g32p_row02_traceSegment_100_2322_0013, g32p_row02_traceSegment_100_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2349 13 14, g32p_row02_traceSegment_100_2349_0013, g32p_row02_traceSegment_100_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2322 27 27, g32p_row02_traceSegment_100_2322_0027, g32p_row02_traceSegment_100_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2268 54 54, g32p_row02_traceSegment_100_2268_0054, g32p_row02_traceSegment_100_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2160 108 108, g32p_row02_traceSegment_100_2160_0108, g32p_row02_traceSegment_100_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2389 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2376 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2376 13 14, g32p_row02_traceSegment_100_2376_0013, g32p_row02_traceSegment_100_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2403 13 14, g32p_row02_traceSegment_100_2403_0013, g32p_row02_traceSegment_100_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2376 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2376 27 27, g32p_row02_traceSegment_100_2376_0027, g32p_row02_traceSegment_100_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2443 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2430 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2430 13 14, g32p_row02_traceSegment_100_2430_0013, g32p_row02_traceSegment_100_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2457 13 14, g32p_row02_traceSegment_100_2457_0013, g32p_row02_traceSegment_100_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2430 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2430 27 27, g32p_row02_traceSegment_100_2430_0027, g32p_row02_traceSegment_100_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 2376 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2376 54 54, g32p_row02_traceSegment_100_2376_0054, g32p_row02_traceSegment_100_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2484 13 14, g32p_row02_traceSegment_100_2484_0013, g32p_row02_traceSegment_100_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2511 13 14, g32p_row02_traceSegment_100_2511_0013, g32p_row02_traceSegment_100_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2484 27 27, g32p_row02_traceSegment_100_2484_0027, g32p_row02_traceSegment_100_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2538 13 14, g32p_row02_traceSegment_100_2538_0013, g32p_row02_traceSegment_100_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2565 13 14, g32p_row02_traceSegment_100_2565_0013, g32p_row02_traceSegment_100_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2538 27 27, g32p_row02_traceSegment_100_2538_0027, g32p_row02_traceSegment_100_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2484 54 54, g32p_row02_traceSegment_100_2484_0054, g32p_row02_traceSegment_100_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 2376 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2376 108 108, g32p_row02_traceSegment_100_2376_0108, g32p_row02_traceSegment_100_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_100 2160 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2160 216 216, g32p_row02_traceSegment_100_2160_0216, g32p_row02_traceSegment_100_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_100 1728 864 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1728 432 432, g32p_row02_traceSegment_100_1728_0432, g32p_row02_traceSegment_100_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2592 13 14, g32p_row02_traceSegment_100_2592_0013, g32p_row02_traceSegment_100_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2619 13 14, g32p_row02_traceSegment_100_2619_0013, g32p_row02_traceSegment_100_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2592 27 27, g32p_row02_traceSegment_100_2592_0027, g32p_row02_traceSegment_100_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2646 13 14, g32p_row02_traceSegment_100_2646_0013, g32p_row02_traceSegment_100_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2673 13 14, g32p_row02_traceSegment_100_2673_0013, g32p_row02_traceSegment_100_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2646 27 27, g32p_row02_traceSegment_100_2646_0027, g32p_row02_traceSegment_100_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2592 54 54, g32p_row02_traceSegment_100_2592_0054, g32p_row02_traceSegment_100_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2700 13 14, g32p_row02_traceSegment_100_2700_0013, g32p_row02_traceSegment_100_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2727 13 14, g32p_row02_traceSegment_100_2727_0013, g32p_row02_traceSegment_100_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2700 27 27, g32p_row02_traceSegment_100_2700_0027, g32p_row02_traceSegment_100_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2754 13 14, g32p_row02_traceSegment_100_2754_0013, g32p_row02_traceSegment_100_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2781 13 14, g32p_row02_traceSegment_100_2781_0013, g32p_row02_traceSegment_100_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2754 27 27, g32p_row02_traceSegment_100_2754_0027, g32p_row02_traceSegment_100_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2700 54 54, g32p_row02_traceSegment_100_2700_0054, g32p_row02_traceSegment_100_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2592 108 108, g32p_row02_traceSegment_100_2592_0108, g32p_row02_traceSegment_100_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2808 13 14, g32p_row02_traceSegment_100_2808_0013, g32p_row02_traceSegment_100_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2835 13 14, g32p_row02_traceSegment_100_2835_0013, g32p_row02_traceSegment_100_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2808 27 27, g32p_row02_traceSegment_100_2808_0027, g32p_row02_traceSegment_100_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2862 13 14, g32p_row02_traceSegment_100_2862_0013, g32p_row02_traceSegment_100_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2889 13 14, g32p_row02_traceSegment_100_2889_0013, g32p_row02_traceSegment_100_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2862 27 27, g32p_row02_traceSegment_100_2862_0027, g32p_row02_traceSegment_100_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2808 54 54, g32p_row02_traceSegment_100_2808_0054, g32p_row02_traceSegment_100_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2916 13 14, g32p_row02_traceSegment_100_2916_0013, g32p_row02_traceSegment_100_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2943 13 14, g32p_row02_traceSegment_100_2943_0013, g32p_row02_traceSegment_100_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2916 27 27, g32p_row02_traceSegment_100_2916_0027, g32p_row02_traceSegment_100_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2970 13 14, g32p_row02_traceSegment_100_2970_0013, g32p_row02_traceSegment_100_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2997 13 14, g32p_row02_traceSegment_100_2997_0013, g32p_row02_traceSegment_100_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2970 27 27, g32p_row02_traceSegment_100_2970_0027, g32p_row02_traceSegment_100_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2916 54 54, g32p_row02_traceSegment_100_2916_0054, g32p_row02_traceSegment_100_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2808 108 108, g32p_row02_traceSegment_100_2808_0108, g32p_row02_traceSegment_100_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_100 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2592 216 216, g32p_row02_traceSegment_100_2592_0216, g32p_row02_traceSegment_100_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3024 13 14, g32p_row02_traceSegment_100_3024_0013, g32p_row02_traceSegment_100_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3051 13 14, g32p_row02_traceSegment_100_3051_0013, g32p_row02_traceSegment_100_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3024 27 27, g32p_row02_traceSegment_100_3024_0027, g32p_row02_traceSegment_100_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3078 13 14, g32p_row02_traceSegment_100_3078_0013, g32p_row02_traceSegment_100_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3105 13 14, g32p_row02_traceSegment_100_3105_0013, g32p_row02_traceSegment_100_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3078 27 27, g32p_row02_traceSegment_100_3078_0027, g32p_row02_traceSegment_100_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3024 54 54, g32p_row02_traceSegment_100_3024_0054, g32p_row02_traceSegment_100_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3132 13 14, g32p_row02_traceSegment_100_3132_0013, g32p_row02_traceSegment_100_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3159 13 14, g32p_row02_traceSegment_100_3159_0013, g32p_row02_traceSegment_100_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3132 27 27, g32p_row02_traceSegment_100_3132_0027, g32p_row02_traceSegment_100_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3186 13 14, g32p_row02_traceSegment_100_3186_0013, g32p_row02_traceSegment_100_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3213 13 14, g32p_row02_traceSegment_100_3213_0013, g32p_row02_traceSegment_100_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3186 27 27, g32p_row02_traceSegment_100_3186_0027, g32p_row02_traceSegment_100_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3132 54 54, g32p_row02_traceSegment_100_3132_0054, g32p_row02_traceSegment_100_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3024 108 108, g32p_row02_traceSegment_100_3024_0108, g32p_row02_traceSegment_100_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3240 13 14, g32p_row02_traceSegment_100_3240_0013, g32p_row02_traceSegment_100_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3267 13 14, g32p_row02_traceSegment_100_3267_0013, g32p_row02_traceSegment_100_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3240 27 27, g32p_row02_traceSegment_100_3240_0027, g32p_row02_traceSegment_100_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3294 13 14, g32p_row02_traceSegment_100_3294_0013, g32p_row02_traceSegment_100_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3321 13 14, g32p_row02_traceSegment_100_3321_0013, g32p_row02_traceSegment_100_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3294 27 27, g32p_row02_traceSegment_100_3294_0027, g32p_row02_traceSegment_100_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3240 54 54, g32p_row02_traceSegment_100_3240_0054, g32p_row02_traceSegment_100_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3348 13 14, g32p_row02_traceSegment_100_3348_0013, g32p_row02_traceSegment_100_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3375 13 14, g32p_row02_traceSegment_100_3375_0013, g32p_row02_traceSegment_100_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3348 27 27, g32p_row02_traceSegment_100_3348_0027, g32p_row02_traceSegment_100_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3402 13 14, g32p_row02_traceSegment_100_3402_0013, g32p_row02_traceSegment_100_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_100 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_100 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_100_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_100 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3429 13 14, g32p_row02_traceSegment_100_3429_0013, g32p_row02_traceSegment_100_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_100 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3402 27 27, g32p_row02_traceSegment_100_3402_0027, g32p_row02_traceSegment_100_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_100 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3348 54 54, g32p_row02_traceSegment_100_3348_0054, g32p_row02_traceSegment_100_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_100 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3240 108 108, g32p_row02_traceSegment_100_3240_0108, g32p_row02_traceSegment_100_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_100_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_100 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 3024 216 216, g32p_row02_traceSegment_100_3024_0216, g32p_row02_traceSegment_100_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_100_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_100 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 2592 432 432, g32p_row02_traceSegment_100_2592_0432, g32p_row02_traceSegment_100_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_100_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_100 1728 1728 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 1728 864 864, g32p_row02_traceSegment_100_1728_0864, g32p_row02_traceSegment_100_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_100_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_100 0 3456 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_100 0 1728 1728, g32p_row02_traceSegment_100_0000_1728, g32p_row02_traceSegment_100_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 100 = [0, 0, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_100_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_101_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 0 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 0 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 0 13 14, g32p_row02_traceSegment_101_0000_0013, g32p_row02_traceSegment_101_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 27 13 14, g32p_row02_traceSegment_101_0027_0013, g32p_row02_traceSegment_101_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 0 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 0 27 27, g32p_row02_traceSegment_101_0000_0027, g32p_row02_traceSegment_101_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 54 13 14, g32p_row02_traceSegment_101_0054_0013, g32p_row02_traceSegment_101_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 81 13 14, g32p_row02_traceSegment_101_0081_0013, g32p_row02_traceSegment_101_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 54 27 27, g32p_row02_traceSegment_101_0054_0027, g32p_row02_traceSegment_101_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 0 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 0 54 54, g32p_row02_traceSegment_101_0000_0054, g32p_row02_traceSegment_101_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 108 13 14, g32p_row02_traceSegment_101_0108_0013, g32p_row02_traceSegment_101_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 135 13 14, g32p_row02_traceSegment_101_0135_0013, g32p_row02_traceSegment_101_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 108 27 27, g32p_row02_traceSegment_101_0108_0027, g32p_row02_traceSegment_101_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 162 13 14, g32p_row02_traceSegment_101_0162_0013, g32p_row02_traceSegment_101_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 189 13 14, g32p_row02_traceSegment_101_0189_0013, g32p_row02_traceSegment_101_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 162 27 27, g32p_row02_traceSegment_101_0162_0027, g32p_row02_traceSegment_101_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 108 54 54, g32p_row02_traceSegment_101_0108_0054, g32p_row02_traceSegment_101_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 0 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 0 108 108, g32p_row02_traceSegment_101_0000_0108, g32p_row02_traceSegment_101_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 216 13 14, g32p_row02_traceSegment_101_0216_0013, g32p_row02_traceSegment_101_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 243 13 14, g32p_row02_traceSegment_101_0243_0013, g32p_row02_traceSegment_101_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 216 27 27, g32p_row02_traceSegment_101_0216_0027, g32p_row02_traceSegment_101_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 270 13 14, g32p_row02_traceSegment_101_0270_0013, g32p_row02_traceSegment_101_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 297 13 14, g32p_row02_traceSegment_101_0297_0013, g32p_row02_traceSegment_101_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 270 27 27, g32p_row02_traceSegment_101_0270_0027, g32p_row02_traceSegment_101_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 216 54 54, g32p_row02_traceSegment_101_0216_0054, g32p_row02_traceSegment_101_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 324 13 14, g32p_row02_traceSegment_101_0324_0013, g32p_row02_traceSegment_101_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 351 13 14, g32p_row02_traceSegment_101_0351_0013, g32p_row02_traceSegment_101_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 324 27 27, g32p_row02_traceSegment_101_0324_0027, g32p_row02_traceSegment_101_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 378 13 14, g32p_row02_traceSegment_101_0378_0013, g32p_row02_traceSegment_101_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 405 13 14, g32p_row02_traceSegment_101_0405_0013, g32p_row02_traceSegment_101_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 378 27 27, g32p_row02_traceSegment_101_0378_0027, g32p_row02_traceSegment_101_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 324 54 54, g32p_row02_traceSegment_101_0324_0054, g32p_row02_traceSegment_101_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 216 108 108, g32p_row02_traceSegment_101_0216_0108, g32p_row02_traceSegment_101_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_101 0 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 0 216 216, g32p_row02_traceSegment_101_0000_0216, g32p_row02_traceSegment_101_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 432 13 14, g32p_row02_traceSegment_101_0432_0013, g32p_row02_traceSegment_101_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 459 13 14, g32p_row02_traceSegment_101_0459_0013, g32p_row02_traceSegment_101_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 432 27 27, g32p_row02_traceSegment_101_0432_0027, g32p_row02_traceSegment_101_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 486 13 14, g32p_row02_traceSegment_101_0486_0013, g32p_row02_traceSegment_101_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 513 13 14, g32p_row02_traceSegment_101_0513_0013, g32p_row02_traceSegment_101_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 486 27 27, g32p_row02_traceSegment_101_0486_0027, g32p_row02_traceSegment_101_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 432 54 54, g32p_row02_traceSegment_101_0432_0054, g32p_row02_traceSegment_101_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 540 13 14, g32p_row02_traceSegment_101_0540_0013, g32p_row02_traceSegment_101_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 567 13 14, g32p_row02_traceSegment_101_0567_0013, g32p_row02_traceSegment_101_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 540 27 27, g32p_row02_traceSegment_101_0540_0027, g32p_row02_traceSegment_101_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 594 13 14, g32p_row02_traceSegment_101_0594_0013, g32p_row02_traceSegment_101_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 621 13 14, g32p_row02_traceSegment_101_0621_0013, g32p_row02_traceSegment_101_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 594 27 27, g32p_row02_traceSegment_101_0594_0027, g32p_row02_traceSegment_101_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 540 54 54, g32p_row02_traceSegment_101_0540_0054, g32p_row02_traceSegment_101_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 432 108 108, g32p_row02_traceSegment_101_0432_0108, g32p_row02_traceSegment_101_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 648 13 14, g32p_row02_traceSegment_101_0648_0013, g32p_row02_traceSegment_101_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 675 13 14, g32p_row02_traceSegment_101_0675_0013, g32p_row02_traceSegment_101_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 648 27 27, g32p_row02_traceSegment_101_0648_0027, g32p_row02_traceSegment_101_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 702 13 14, g32p_row02_traceSegment_101_0702_0013, g32p_row02_traceSegment_101_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 729 13 14, g32p_row02_traceSegment_101_0729_0013, g32p_row02_traceSegment_101_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 702 27 27, g32p_row02_traceSegment_101_0702_0027, g32p_row02_traceSegment_101_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 648 54 54, g32p_row02_traceSegment_101_0648_0054, g32p_row02_traceSegment_101_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 756 13 14, g32p_row02_traceSegment_101_0756_0013, g32p_row02_traceSegment_101_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 783 13 14, g32p_row02_traceSegment_101_0783_0013, g32p_row02_traceSegment_101_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 756 27 27, g32p_row02_traceSegment_101_0756_0027, g32p_row02_traceSegment_101_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 810 13 14, g32p_row02_traceSegment_101_0810_0013, g32p_row02_traceSegment_101_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 837 13 14, g32p_row02_traceSegment_101_0837_0013, g32p_row02_traceSegment_101_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 810 27 27, g32p_row02_traceSegment_101_0810_0027, g32p_row02_traceSegment_101_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 756 54 54, g32p_row02_traceSegment_101_0756_0054, g32p_row02_traceSegment_101_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 648 108 108, g32p_row02_traceSegment_101_0648_0108, g32p_row02_traceSegment_101_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_101 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 432 216 216, g32p_row02_traceSegment_101_0432_0216, g32p_row02_traceSegment_101_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_101 0 864 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 0 432 432, g32p_row02_traceSegment_101_0000_0432, g32p_row02_traceSegment_101_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 864 13 14, g32p_row02_traceSegment_101_0864_0013, g32p_row02_traceSegment_101_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 891 13 14, g32p_row02_traceSegment_101_0891_0013, g32p_row02_traceSegment_101_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 864 27 27, g32p_row02_traceSegment_101_0864_0027, g32p_row02_traceSegment_101_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 918 13 14, g32p_row02_traceSegment_101_0918_0013, g32p_row02_traceSegment_101_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 945 13 14, g32p_row02_traceSegment_101_0945_0013, g32p_row02_traceSegment_101_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 918 27 27, g32p_row02_traceSegment_101_0918_0027, g32p_row02_traceSegment_101_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 864 54 54, g32p_row02_traceSegment_101_0864_0054, g32p_row02_traceSegment_101_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 972 13 14, g32p_row02_traceSegment_101_0972_0013, g32p_row02_traceSegment_101_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 999 13 14, g32p_row02_traceSegment_101_0999_0013, g32p_row02_traceSegment_101_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 972 27 27, g32p_row02_traceSegment_101_0972_0027, g32p_row02_traceSegment_101_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1026 13 14, g32p_row02_traceSegment_101_1026_0013, g32p_row02_traceSegment_101_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1053 13 14, g32p_row02_traceSegment_101_1053_0013, g32p_row02_traceSegment_101_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1026 27 27, g32p_row02_traceSegment_101_1026_0027, g32p_row02_traceSegment_101_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 972 54 54, g32p_row02_traceSegment_101_0972_0054, g32p_row02_traceSegment_101_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 864 108 108, g32p_row02_traceSegment_101_0864_0108, g32p_row02_traceSegment_101_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1080 13 14, g32p_row02_traceSegment_101_1080_0013, g32p_row02_traceSegment_101_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1107 13 14, g32p_row02_traceSegment_101_1107_0013, g32p_row02_traceSegment_101_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1080 27 27, g32p_row02_traceSegment_101_1080_0027, g32p_row02_traceSegment_101_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1134 13 14, g32p_row02_traceSegment_101_1134_0013, g32p_row02_traceSegment_101_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1161 13 14, g32p_row02_traceSegment_101_1161_0013, g32p_row02_traceSegment_101_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1134 27 27, g32p_row02_traceSegment_101_1134_0027, g32p_row02_traceSegment_101_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1080 54 54, g32p_row02_traceSegment_101_1080_0054, g32p_row02_traceSegment_101_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1188 13 14, g32p_row02_traceSegment_101_1188_0013, g32p_row02_traceSegment_101_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1215 13 14, g32p_row02_traceSegment_101_1215_0013, g32p_row02_traceSegment_101_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1188 27 27, g32p_row02_traceSegment_101_1188_0027, g32p_row02_traceSegment_101_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1242 13 14, g32p_row02_traceSegment_101_1242_0013, g32p_row02_traceSegment_101_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1269 13 14, g32p_row02_traceSegment_101_1269_0013, g32p_row02_traceSegment_101_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1242 27 27, g32p_row02_traceSegment_101_1242_0027, g32p_row02_traceSegment_101_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1188 54 54, g32p_row02_traceSegment_101_1188_0054, g32p_row02_traceSegment_101_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1080 108 108, g32p_row02_traceSegment_101_1080_0108, g32p_row02_traceSegment_101_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_101 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 864 216 216, g32p_row02_traceSegment_101_0864_0216, g32p_row02_traceSegment_101_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1296 13 14, g32p_row02_traceSegment_101_1296_0013, g32p_row02_traceSegment_101_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1323 13 14, g32p_row02_traceSegment_101_1323_0013, g32p_row02_traceSegment_101_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1296 27 27, g32p_row02_traceSegment_101_1296_0027, g32p_row02_traceSegment_101_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1350 13 14, g32p_row02_traceSegment_101_1350_0013, g32p_row02_traceSegment_101_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1377 13 14, g32p_row02_traceSegment_101_1377_0013, g32p_row02_traceSegment_101_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1350 27 27, g32p_row02_traceSegment_101_1350_0027, g32p_row02_traceSegment_101_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1296 54 54, g32p_row02_traceSegment_101_1296_0054, g32p_row02_traceSegment_101_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1404 13 14, g32p_row02_traceSegment_101_1404_0013, g32p_row02_traceSegment_101_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1431 13 14, g32p_row02_traceSegment_101_1431_0013, g32p_row02_traceSegment_101_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1404 27 27, g32p_row02_traceSegment_101_1404_0027, g32p_row02_traceSegment_101_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1458 13 14, g32p_row02_traceSegment_101_1458_0013, g32p_row02_traceSegment_101_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1485 13 14, g32p_row02_traceSegment_101_1485_0013, g32p_row02_traceSegment_101_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1458 27 27, g32p_row02_traceSegment_101_1458_0027, g32p_row02_traceSegment_101_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1404 54 54, g32p_row02_traceSegment_101_1404_0054, g32p_row02_traceSegment_101_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1296 108 108, g32p_row02_traceSegment_101_1296_0108, g32p_row02_traceSegment_101_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1512 13 14, g32p_row02_traceSegment_101_1512_0013, g32p_row02_traceSegment_101_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1539 13 14, g32p_row02_traceSegment_101_1539_0013, g32p_row02_traceSegment_101_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1512 27 27, g32p_row02_traceSegment_101_1512_0027, g32p_row02_traceSegment_101_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1566 13 14, g32p_row02_traceSegment_101_1566_0013, g32p_row02_traceSegment_101_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1593 13 14, g32p_row02_traceSegment_101_1593_0013, g32p_row02_traceSegment_101_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1566 27 27, g32p_row02_traceSegment_101_1566_0027, g32p_row02_traceSegment_101_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1512 54 54, g32p_row02_traceSegment_101_1512_0054, g32p_row02_traceSegment_101_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1620 13 14, g32p_row02_traceSegment_101_1620_0013, g32p_row02_traceSegment_101_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1647 13 14, g32p_row02_traceSegment_101_1647_0013, g32p_row02_traceSegment_101_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1620 27 27, g32p_row02_traceSegment_101_1620_0027, g32p_row02_traceSegment_101_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1674 13 14, g32p_row02_traceSegment_101_1674_0013, g32p_row02_traceSegment_101_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1701 13 14, g32p_row02_traceSegment_101_1701_0013, g32p_row02_traceSegment_101_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1674 27 27, g32p_row02_traceSegment_101_1674_0027, g32p_row02_traceSegment_101_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1620 54 54, g32p_row02_traceSegment_101_1620_0054, g32p_row02_traceSegment_101_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1512 108 108, g32p_row02_traceSegment_101_1512_0108, g32p_row02_traceSegment_101_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_101 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1296 216 216, g32p_row02_traceSegment_101_1296_0216, g32p_row02_traceSegment_101_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_101 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 864 432 432, g32p_row02_traceSegment_101_0864_0432, g32p_row02_traceSegment_101_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_101 0 1728 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 0 864 864, g32p_row02_traceSegment_101_0000_0864, g32p_row02_traceSegment_101_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1728 13 14, g32p_row02_traceSegment_101_1728_0013, g32p_row02_traceSegment_101_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1755 13 14, g32p_row02_traceSegment_101_1755_0013, g32p_row02_traceSegment_101_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1728 27 27, g32p_row02_traceSegment_101_1728_0027, g32p_row02_traceSegment_101_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1782 13 14, g32p_row02_traceSegment_101_1782_0013, g32p_row02_traceSegment_101_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1809 13 14, g32p_row02_traceSegment_101_1809_0013, g32p_row02_traceSegment_101_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1782 27 27, g32p_row02_traceSegment_101_1782_0027, g32p_row02_traceSegment_101_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1728 54 54, g32p_row02_traceSegment_101_1728_0054, g32p_row02_traceSegment_101_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1836 13 14, g32p_row02_traceSegment_101_1836_0013, g32p_row02_traceSegment_101_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1863 13 14, g32p_row02_traceSegment_101_1863_0013, g32p_row02_traceSegment_101_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1836 27 27, g32p_row02_traceSegment_101_1836_0027, g32p_row02_traceSegment_101_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1890 13 14, g32p_row02_traceSegment_101_1890_0013, g32p_row02_traceSegment_101_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1917 13 14, g32p_row02_traceSegment_101_1917_0013, g32p_row02_traceSegment_101_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1890 27 27, g32p_row02_traceSegment_101_1890_0027, g32p_row02_traceSegment_101_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1836 54 54, g32p_row02_traceSegment_101_1836_0054, g32p_row02_traceSegment_101_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1728 108 108, g32p_row02_traceSegment_101_1728_0108, g32p_row02_traceSegment_101_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1944 13 14, g32p_row02_traceSegment_101_1944_0013, g32p_row02_traceSegment_101_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1971 13 14, g32p_row02_traceSegment_101_1971_0013, g32p_row02_traceSegment_101_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1944 27 27, g32p_row02_traceSegment_101_1944_0027, g32p_row02_traceSegment_101_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1998 13 14, g32p_row02_traceSegment_101_1998_0013, g32p_row02_traceSegment_101_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2025 13 14, g32p_row02_traceSegment_101_2025_0013, g32p_row02_traceSegment_101_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1998 27 27, g32p_row02_traceSegment_101_1998_0027, g32p_row02_traceSegment_101_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1944 54 54, g32p_row02_traceSegment_101_1944_0054, g32p_row02_traceSegment_101_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2052 13 14, g32p_row02_traceSegment_101_2052_0013, g32p_row02_traceSegment_101_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2079 13 14, g32p_row02_traceSegment_101_2079_0013, g32p_row02_traceSegment_101_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2052 27 27, g32p_row02_traceSegment_101_2052_0027, g32p_row02_traceSegment_101_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2106 13 14, g32p_row02_traceSegment_101_2106_0013, g32p_row02_traceSegment_101_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2133 13 14, g32p_row02_traceSegment_101_2133_0013, g32p_row02_traceSegment_101_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2106 27 27, g32p_row02_traceSegment_101_2106_0027, g32p_row02_traceSegment_101_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2052 54 54, g32p_row02_traceSegment_101_2052_0054, g32p_row02_traceSegment_101_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1944 108 108, g32p_row02_traceSegment_101_1944_0108, g32p_row02_traceSegment_101_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_101 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1728 216 216, g32p_row02_traceSegment_101_1728_0216, g32p_row02_traceSegment_101_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2160 13 14, g32p_row02_traceSegment_101_2160_0013, g32p_row02_traceSegment_101_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2187 13 14, g32p_row02_traceSegment_101_2187_0013, g32p_row02_traceSegment_101_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2160 27 27, g32p_row02_traceSegment_101_2160_0027, g32p_row02_traceSegment_101_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2214 13 14, g32p_row02_traceSegment_101_2214_0013, g32p_row02_traceSegment_101_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2241 13 14, g32p_row02_traceSegment_101_2241_0013, g32p_row02_traceSegment_101_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2214 27 27, g32p_row02_traceSegment_101_2214_0027, g32p_row02_traceSegment_101_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2160 54 54, g32p_row02_traceSegment_101_2160_0054, g32p_row02_traceSegment_101_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2268 13 14, g32p_row02_traceSegment_101_2268_0013, g32p_row02_traceSegment_101_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2295 13 14, g32p_row02_traceSegment_101_2295_0013, g32p_row02_traceSegment_101_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2268 27 27, g32p_row02_traceSegment_101_2268_0027, g32p_row02_traceSegment_101_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2322 13 14, g32p_row02_traceSegment_101_2322_0013, g32p_row02_traceSegment_101_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2349 13 14, g32p_row02_traceSegment_101_2349_0013, g32p_row02_traceSegment_101_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2322 27 27, g32p_row02_traceSegment_101_2322_0027, g32p_row02_traceSegment_101_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2268 54 54, g32p_row02_traceSegment_101_2268_0054, g32p_row02_traceSegment_101_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2160 108 108, g32p_row02_traceSegment_101_2160_0108, g32p_row02_traceSegment_101_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2376 13 14, g32p_row02_traceSegment_101_2376_0013, g32p_row02_traceSegment_101_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2403 13 14, g32p_row02_traceSegment_101_2403_0013, g32p_row02_traceSegment_101_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2376 27 27, g32p_row02_traceSegment_101_2376_0027, g32p_row02_traceSegment_101_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2430 13 14, g32p_row02_traceSegment_101_2430_0013, g32p_row02_traceSegment_101_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2457 13 14, g32p_row02_traceSegment_101_2457_0013, g32p_row02_traceSegment_101_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2430 27 27, g32p_row02_traceSegment_101_2430_0027, g32p_row02_traceSegment_101_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2376 54 54, g32p_row02_traceSegment_101_2376_0054, g32p_row02_traceSegment_101_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2484 13 14, g32p_row02_traceSegment_101_2484_0013, g32p_row02_traceSegment_101_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2511 13 14, g32p_row02_traceSegment_101_2511_0013, g32p_row02_traceSegment_101_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2484 27 27, g32p_row02_traceSegment_101_2484_0027, g32p_row02_traceSegment_101_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2538 13 14, g32p_row02_traceSegment_101_2538_0013, g32p_row02_traceSegment_101_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2565 13 14, g32p_row02_traceSegment_101_2565_0013, g32p_row02_traceSegment_101_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2538 27 27, g32p_row02_traceSegment_101_2538_0027, g32p_row02_traceSegment_101_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2484 54 54, g32p_row02_traceSegment_101_2484_0054, g32p_row02_traceSegment_101_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2376 108 108, g32p_row02_traceSegment_101_2376_0108, g32p_row02_traceSegment_101_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_101 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2160 216 216, g32p_row02_traceSegment_101_2160_0216, g32p_row02_traceSegment_101_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_101 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1728 432 432, g32p_row02_traceSegment_101_1728_0432, g32p_row02_traceSegment_101_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2592 13 14, g32p_row02_traceSegment_101_2592_0013, g32p_row02_traceSegment_101_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2619 13 14, g32p_row02_traceSegment_101_2619_0013, g32p_row02_traceSegment_101_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2592 27 27, g32p_row02_traceSegment_101_2592_0027, g32p_row02_traceSegment_101_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2646 13 14, g32p_row02_traceSegment_101_2646_0013, g32p_row02_traceSegment_101_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2673 13 14, g32p_row02_traceSegment_101_2673_0013, g32p_row02_traceSegment_101_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2646 27 27, g32p_row02_traceSegment_101_2646_0027, g32p_row02_traceSegment_101_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2592 54 54, g32p_row02_traceSegment_101_2592_0054, g32p_row02_traceSegment_101_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2700 13 14, g32p_row02_traceSegment_101_2700_0013, g32p_row02_traceSegment_101_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2727 13 14, g32p_row02_traceSegment_101_2727_0013, g32p_row02_traceSegment_101_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2700 27 27, g32p_row02_traceSegment_101_2700_0027, g32p_row02_traceSegment_101_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2754 13 14, g32p_row02_traceSegment_101_2754_0013, g32p_row02_traceSegment_101_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2781 13 14, g32p_row02_traceSegment_101_2781_0013, g32p_row02_traceSegment_101_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2754 27 27, g32p_row02_traceSegment_101_2754_0027, g32p_row02_traceSegment_101_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2700 54 54, g32p_row02_traceSegment_101_2700_0054, g32p_row02_traceSegment_101_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2592 108 108, g32p_row02_traceSegment_101_2592_0108, g32p_row02_traceSegment_101_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2808 13 14, g32p_row02_traceSegment_101_2808_0013, g32p_row02_traceSegment_101_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2835 13 14, g32p_row02_traceSegment_101_2835_0013, g32p_row02_traceSegment_101_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2808 27 27, g32p_row02_traceSegment_101_2808_0027, g32p_row02_traceSegment_101_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2862 13 14, g32p_row02_traceSegment_101_2862_0013, g32p_row02_traceSegment_101_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2889 13 14, g32p_row02_traceSegment_101_2889_0013, g32p_row02_traceSegment_101_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2862 27 27, g32p_row02_traceSegment_101_2862_0027, g32p_row02_traceSegment_101_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2808 54 54, g32p_row02_traceSegment_101_2808_0054, g32p_row02_traceSegment_101_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2916 13 14, g32p_row02_traceSegment_101_2916_0013, g32p_row02_traceSegment_101_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2943 13 14, g32p_row02_traceSegment_101_2943_0013, g32p_row02_traceSegment_101_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2916 27 27, g32p_row02_traceSegment_101_2916_0027, g32p_row02_traceSegment_101_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2970 13 14, g32p_row02_traceSegment_101_2970_0013, g32p_row02_traceSegment_101_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2997 13 14, g32p_row02_traceSegment_101_2997_0013, g32p_row02_traceSegment_101_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2970 27 27, g32p_row02_traceSegment_101_2970_0027, g32p_row02_traceSegment_101_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2916 54 54, g32p_row02_traceSegment_101_2916_0054, g32p_row02_traceSegment_101_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2808 108 108, g32p_row02_traceSegment_101_2808_0108, g32p_row02_traceSegment_101_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_101 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2592 216 216, g32p_row02_traceSegment_101_2592_0216, g32p_row02_traceSegment_101_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3024 13 14, g32p_row02_traceSegment_101_3024_0013, g32p_row02_traceSegment_101_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3051 13 14, g32p_row02_traceSegment_101_3051_0013, g32p_row02_traceSegment_101_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3024 27 27, g32p_row02_traceSegment_101_3024_0027, g32p_row02_traceSegment_101_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3078 13 14, g32p_row02_traceSegment_101_3078_0013, g32p_row02_traceSegment_101_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3105 13 14, g32p_row02_traceSegment_101_3105_0013, g32p_row02_traceSegment_101_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3078 27 27, g32p_row02_traceSegment_101_3078_0027, g32p_row02_traceSegment_101_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3024 54 54, g32p_row02_traceSegment_101_3024_0054, g32p_row02_traceSegment_101_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3132 13 14, g32p_row02_traceSegment_101_3132_0013, g32p_row02_traceSegment_101_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3159 13 14, g32p_row02_traceSegment_101_3159_0013, g32p_row02_traceSegment_101_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3132 27 27, g32p_row02_traceSegment_101_3132_0027, g32p_row02_traceSegment_101_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3186 13 14, g32p_row02_traceSegment_101_3186_0013, g32p_row02_traceSegment_101_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3213 13 14, g32p_row02_traceSegment_101_3213_0013, g32p_row02_traceSegment_101_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3186 27 27, g32p_row02_traceSegment_101_3186_0027, g32p_row02_traceSegment_101_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3132 54 54, g32p_row02_traceSegment_101_3132_0054, g32p_row02_traceSegment_101_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3024 108 108, g32p_row02_traceSegment_101_3024_0108, g32p_row02_traceSegment_101_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3240 13 14, g32p_row02_traceSegment_101_3240_0013, g32p_row02_traceSegment_101_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3267 13 14, g32p_row02_traceSegment_101_3267_0013, g32p_row02_traceSegment_101_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3240 27 27, g32p_row02_traceSegment_101_3240_0027, g32p_row02_traceSegment_101_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3294 13 14, g32p_row02_traceSegment_101_3294_0013, g32p_row02_traceSegment_101_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3321 13 14, g32p_row02_traceSegment_101_3321_0013, g32p_row02_traceSegment_101_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3294 27 27, g32p_row02_traceSegment_101_3294_0027, g32p_row02_traceSegment_101_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3240 54 54, g32p_row02_traceSegment_101_3240_0054, g32p_row02_traceSegment_101_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3348 13 14, g32p_row02_traceSegment_101_3348_0013, g32p_row02_traceSegment_101_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3375 13 14, g32p_row02_traceSegment_101_3375_0013, g32p_row02_traceSegment_101_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3348 27 27, g32p_row02_traceSegment_101_3348_0027, g32p_row02_traceSegment_101_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3402 13 14, g32p_row02_traceSegment_101_3402_0013, g32p_row02_traceSegment_101_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_101 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_101 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_101_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_101 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3429 13 14, g32p_row02_traceSegment_101_3429_0013, g32p_row02_traceSegment_101_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_101 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3402 27 27, g32p_row02_traceSegment_101_3402_0027, g32p_row02_traceSegment_101_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_101 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3348 54 54, g32p_row02_traceSegment_101_3348_0054, g32p_row02_traceSegment_101_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_101 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3240 108 108, g32p_row02_traceSegment_101_3240_0108, g32p_row02_traceSegment_101_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_101_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_101 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 3024 216 216, g32p_row02_traceSegment_101_3024_0216, g32p_row02_traceSegment_101_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_101_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_101 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 2592 432 432, g32p_row02_traceSegment_101_2592_0432, g32p_row02_traceSegment_101_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_101_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_101 1728 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 1728 864 864, g32p_row02_traceSegment_101_1728_0864, g32p_row02_traceSegment_101_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_101_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_101 0 3456 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_101 0 1728 1728, g32p_row02_traceSegment_101_0000_1728, g32p_row02_traceSegment_101_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_101_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 98) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 98) (g32p_literalTraceValue 1 98)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_098]
  decide +kernel

theorem g32p_row02_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 99) (g32p_literalTraceValue 1 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_099]
  decide +kernel

theorem g32p_row02_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 100) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 100) (g32p_literalTraceValue 1 100)
      [1, -1, 1] [31104, 31104, 31104] = true := by
  rw [g32p_row02_traceCoefficients_100]
  decide +kernel

theorem g32p_row02_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 101) (g32p_literalTraceValue 1 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row02_traceCoefficients_101]
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32p_supplier_coinduced_zero (i : Fin 51)
    (classify : (g32p_recordedSuppliers i).H → Fin 102)
    (hconj : ∀ h : (g32p_recordedSuppliers i).H, IsConj (h : g32p_G) (g32p_literalRepresentative (classify h)))
    (support : Finset (Fin 102)) (hmem : ∀ h : (g32p_recordedSuppliers i).H, classify h ∈ support)
    (hsep : Function.Injective (fun c => ConjClasses.mk (g32p_literalRepresentative c)))
    (c : Fin 102) (hc : c ∉ support) (conjugate : Bool) :
    (g32p_recordedCoinduced i conjugate).character (g32p_literalRepresentative c) = 0 := by
  classical
  have hx (x : g32p_G) :
      x * g32p_literalRepresentative c * x⁻¹ ∉ (g32p_recordedSuppliers i).H := by
    intro hm
    let h : (g32p_recordedSuppliers i).H := ⟨_, hm⟩
    have hh : IsConj (g32p_literalRepresentative c) (h : g32p_G) :=
      isConj_iff.mpr ⟨x, rfl⟩
    have he : c = classify h := hsep (ConjClasses.mk_eq_mk_iff_isConj.mpr (hh.trans (hconj h)))
    apply hc
    rw [he]
    exact hmem h
  rw [g32p_recordedCoinduced_character]
  simp [hx]

theorem g32p_supplier_induction_zero (i : Fin 51) (c : Fin 102) (conjugate : Bool)
    (h : (g32p_recordedCoinduced i conjugate).character (g32p_literalRepresentative c) = 0)
    (variant : Fin 4) :
    (g32p_inductionGenerator i conjugate variant).character (g32p_literalRepresentative c) = 0 := by
  fin_cases variant <;>
    simp [g32p_inductionGenerator, FDRep.char_tensor, g32p_twist_character, h]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row02_generatorIndex : Fin 8 → Fin 408 :=
  ![1, 52, 103, 154, 206, 207, 308, 309]

theorem g32p_row02_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup00_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 1 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 1 g32p_row02_supplierClass
    g32p_row02_supplierClass_isConj g32p_supplierGroup00_support g32p_row02_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row02_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup00_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row02_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 1 c false (g32p_row02_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 1 c true (g32p_row02_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 1 c false (g32p_row02_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 1 c true (g32p_row02_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 1 c false (g32p_row02_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 1 c false (g32p_row02_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 1 c true (g32p_row02_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 1 c true (g32p_row02_coinduced_zero c hc true) 3

theorem g32p_row02_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup00_support →
      g32p_literalTraceValue (g32p_row02_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row02_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup00_support →
      g32p_literalTraceValue (g32p_row02_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row02_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup00_support →
      g32p_literalTraceValue (g32p_row02_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row02_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup00_support →
      g32p_literalTraceValue (g32p_row02_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row02_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup00_support →
      g32p_literalTraceValue (g32p_row02_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row02_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup00_support →
      g32p_literalTraceValue (g32p_row02_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row02_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup00_support →
      g32p_literalTraceValue (g32p_row02_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row02_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup00_support) :
    g32p_literalTraceValue (g32p_row02_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup00_support →
    g32p_literalTraceValue (g32p_row02_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row02_zeroTrace_block_00 r k
  · exact g32p_row02_zeroTrace_block_01 r k
  · exact g32p_row02_zeroTrace_block_02 r k
  · exact g32p_row02_zeroTrace_block_03 r k
  · exact g32p_row02_zeroTrace_block_04 r k
  · exact g32p_row02_zeroTrace_block_05 r k
  · exact g32p_row02_zeroTrace_block_06 r k

theorem g32p_row02_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup00_support) :
    (g32p_recordedInductionGenerators (g32p_row02_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row02_generatorIndex k) c) := by
  rw [g32p_row02_recordedGenerator_zero c hc k, g32p_row02_zeroTrace_arithmetic c k hc]
  norm_num [HurwitzPrymRex_ev]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def g32p_row02_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [10368, 10368, 10368])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 6912, 6912] else [])) else (if i.val < 16 then [3456, 3456, 3456] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [41472, 41472] else (if i.val < 20 then [3456, 3456, 3456] else [3456, 3456, 3456])) else (if i.val < 23 then (if i.val < 22 then [-3456, 0, 3456, 3456] else []) else (if i.val < 24 then [] else [10368, 10368, 10368]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [13824, 13824, 3456] else (if i.val < 27 then [] else [3456, 3456, 3456])) else (if i.val < 29 then [31104, 31104, 31104] else (if i.val < 30 then [10368, 10368] else [3456, 3456, 3456, 3456]))) else (if i.val < 34 then (if i.val < 32 then [3456, 3456, 3456] else (if i.val < 33 then [10368, 10368, 10368] else [])) else (if i.val < 36 then (if i.val < 35 then [3456, 10368, 10368] else [10368, 10368, 10368]) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [3456, 3456] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [3456, 3456, 3456] else (if i.val < 43 then [] else [3456, 3456, 13824, 10368]))) else (if i.val < 47 then (if i.val < 45 then [31104, 31104, 31104] else (if i.val < 46 then [] else [0, 3456])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [0, 0, 3456, 3456] else [-10368])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [3456, 3456, 3456] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [3456, 3456, 3456] else [10368, 10368, 10368]))) else (if i.val < 60 then (if i.val < 58 then [-3456] else (if i.val < 59 then [] else [0, 0, 10368, 10368])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [-38016, 3456, 3456])) else (if i.val < 67 then [3456, 3456, 3456] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [6912, 6912] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [-10368] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [31104, 31104, 31104] else (if i.val < 78 then [3456, 3456, 3456] else [10368, 10368, 10368])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [0, 0, 41472, 41472] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [3456, 3456, 3456] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [3456, 3456, 3456] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [31104, 31104, 31104] else [155520, 155520, 155520])))))))

theorem g32p_row02_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup00_support) :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) c) (g32p_literalTraceValue 1 c)
      [1, -1, 1] (g32p_row02_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row02_tracePolynomial_000
  · exact g32p_row02_tracePolynomial_001
  · exact g32p_row02_tracePolynomial_002
  · exact g32p_row02_tracePolynomial_003
  · exact g32p_row02_tracePolynomial_004
  · exact g32p_row02_tracePolynomial_005
  · exact g32p_row02_tracePolynomial_006
  · exact g32p_row02_tracePolynomial_007
  · exact g32p_row02_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_010
  · exact g32p_row02_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_017
  · exact g32p_row02_tracePolynomial_018
  · exact g32p_row02_tracePolynomial_019
  · exact g32p_row02_tracePolynomial_020
  · exact g32p_row02_tracePolynomial_021
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_023
  · exact g32p_row02_tracePolynomial_024
  · exact g32p_row02_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_027
  · exact g32p_row02_tracePolynomial_028
  · exact g32p_row02_tracePolynomial_029
  · exact g32p_row02_tracePolynomial_030
  · exact g32p_row02_tracePolynomial_031
  · exact g32p_row02_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_034
  · exact g32p_row02_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_037
  · exact g32p_row02_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_040
  · exact g32p_row02_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_043
  · exact g32p_row02_tracePolynomial_044
  · exact g32p_row02_tracePolynomial_045
  · exact g32p_row02_tracePolynomial_046
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_048
  · exact g32p_row02_tracePolynomial_049
  · exact g32p_row02_tracePolynomial_050
  · exact g32p_row02_tracePolynomial_051
  · exact g32p_row02_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_055
  · exact g32p_row02_tracePolynomial_056
  · exact g32p_row02_tracePolynomial_057
  · exact g32p_row02_tracePolynomial_058
  · exact g32p_row02_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_061
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_063
  · exact g32p_row02_tracePolynomial_064
  · exact g32p_row02_tracePolynomial_065
  · exact g32p_row02_tracePolynomial_066
  · exact g32p_row02_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_071
  · exact g32p_row02_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup00_support) hc)
  · exact g32p_row02_tracePolynomial_074
  · exact g32p_row02_tracePolynomial_075
  · exact g32p_row02_tracePolynomial_076
  · exact g32p_row02_tracePolynomial_077
  · exact g32p_row02_tracePolynomial_078
  · exact g32p_row02_tracePolynomial_079
  · exact g32p_row02_tracePolynomial_080
  · exact g32p_row02_tracePolynomial_081
  · exact g32p_row02_tracePolynomial_082
  · exact g32p_row02_tracePolynomial_083
  · exact g32p_row02_tracePolynomial_084
  · exact g32p_row02_tracePolynomial_085
  · exact g32p_row02_tracePolynomial_086
  · exact g32p_row02_tracePolynomial_087
  · exact g32p_row02_tracePolynomial_088
  · exact g32p_row02_tracePolynomial_089
  · exact g32p_row02_tracePolynomial_090
  · exact g32p_row02_tracePolynomial_091
  · exact g32p_row02_tracePolynomial_092
  · exact g32p_row02_tracePolynomial_093
  · exact g32p_row02_tracePolynomial_094
  · exact g32p_row02_tracePolynomial_095
  · exact g32p_row02_tracePolynomial_096
  · exact g32p_row02_tracePolynomial_097
  · exact g32p_row02_tracePolynomial_098
  · exact g32p_row02_tracePolynomial_099
  · exact g32p_row02_tracePolynomial_100
  · exact g32p_row02_tracePolynomial_101

theorem g32p_row02_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 1 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 1 c) := by
  by_cases hc : c ∈ g32p_supplierGroup00_support
  · have hclass (j : Fin 3456) :
        IsConj (g32p_literalRepresentative c) (g32p_row02_groupEquiv j : g32p_G) ↔
          g32p_row02_supplierClassifier j = c := by
      simpa only [g32p_row02_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row02_supplierClass_iff (g32p_row02_groupEquiv j) c
    have hχ (j : Fin 3456) :
        (g32p_recordedSupplierCharacters 1 (g32p_row02_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row02_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 1 (show (g32p_recordedSuppliers 1).H from g32p_row02_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row02_characterValues (g32p_row02_groupEquiv.symm (g32p_row02_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 1).H (g32p_recordedSupplierCharacters 1)
      (g32p_literalRepresentative c) g32p_row02_groupEquiv g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) c 6 3456
      (g32p_literalCentralizer c) (g32p_literalTraceValue 1 c) [1, -1, 1]
      (g32p_row02_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row02_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 1)))
      (g32p_row02_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row02_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

def g32p_supplierVariantTracePair (t d r : HurwitzPrymRex_Zw) (conjugate : Bool)
    (variant : Fin 4) : HurwitzPrymRex_Zw :=
  let a := if conjugate then g32p_eisensteinStar t else t
  ![a, HurwitzPrymRex_Zw.mul a r, HurwitzPrymRex_Zw.mul d a,
    HurwitzPrymRex_Zw.mul (HurwitzPrymRex_Zw.mul d d) a] variant

theorem g32p_supplierVariantTrace_actual (i : Fin 51) (c : Fin 102) (t : HurwitzPrymRex_Zw)
    (hbase : (g32p_recordedCoinduced i false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega t) (conjugate : Bool) (variant : Fin 4) :
    (g32p_inductionGenerator i conjugate variant).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_supplierVariantTracePair t
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) conjugate variant) := by
  have hc : (g32p_recordedCoinduced i true).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_eisensteinStar t) := by
    change (g32p_coinduced _ (g32p_recordedSupplierCharacters i)⁻¹).character _ = _
    rw [g32p_coinduced_character_inverse]
    change star ((g32p_recordedCoinduced i false).character _) = _
    rw [hbase, g32p_eisensteinStar_eval]
  let a := if conjugate then g32p_eisensteinStar t else t
  have hχ : (g32p_recordedCoinduced i conjugate).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega a := by
    cases conjugate
    · exact hbase
    · exact hc
  have ht : g32p_rho.character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalPowerTrace c 0) := by
    simpa only [Fin.val_zero, zero_add, pow_one] using g32p_literalPowerTrace_actual c 0
  have hd := g32p_literalDeterminantPair_eval c
  fin_cases variant
  · change (g32p_recordedCoinduced i conjugate).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega a
    exact hχ
  · change (g32p_inductionGenerator i conjugate 1).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (HurwitzPrymRex_Zw.mul a (g32p_literalPowerTrace c 0))
    rw [g32p_inductionGenerator_tensor_character, hχ, ht,
      HurwitzPrymRex_ev_mul g32h_omega_sq_add]
  · change (g32p_inductionGenerator i conjugate 2).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (HurwitzPrymRex_Zw.mul (g32p_literalDeterminantPair c) a)
    rw [g32p_inductionGenerator_twist_character, hχ,
      HurwitzPrymRex_ev_mul g32h_omega_sq_add, hd]
  · change (g32p_inductionGenerator i conjugate 3).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (HurwitzPrymRex_Zw.mul
        (HurwitzPrymRex_Zw.mul (g32p_literalDeterminantPair c) (g32p_literalDeterminantPair c)) a)
    rw [g32p_inductionGenerator_twist_sq_character, hχ,
      HurwitzPrymRex_ev_mul g32h_omega_sq_add, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      hd, pow_two]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row02_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row02_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row02_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row02_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row02_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row02_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row02_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row02_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
